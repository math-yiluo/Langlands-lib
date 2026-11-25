/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.MapIhom
public import Mathlib.Tactic.CategoryTheory.Slice
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorExchange
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist

/-!
# Tensor products of modules with an invertible structure morphism

Let `F : C ⥤ C` be a lax monoidal functor with invertible tensor comparison and `σ : A ⟶ F A` an
isomorphism of commutative monoids, so that `F` induces an endofunctor `Φ = mapModComap σ` of the
category of `A`-modules commuting with tensor products
(`CategoryTheory.Mod.tensorLeftCompMapModComapIso`). Objects of `IsoAlgebra Φ` are `A`-modules
`K` with an isomorphism `Φ K ≅ K`. Their tensor product `L ⊗_A K` is again such an object
(`CategoryTheory.Mod.isoAlgebraTensor`).

For a further lax monoidal functor `G : C ⥤ D` commuting with `F` and `F' : D ⥤ D` through a
monoidal natural transformation, lifted to an isomorphism `e : Γ ⋙ Φ' ≅ Φ ⋙ Γ` of the induced
functors on modules, the transport `IsoAlgebra.mapOfNatIso e` commutes with these tensor
products (`CategoryTheory.Mod.isoAlgebraTensorCompMapOfNatIsoIso`).
-/

@[expose] public section

universe v u v' u'

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal Endofunctor

namespace CategoryTheory.Mod

open scoped Obj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [BraidedCategory C] [IsCommMonObj A] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {B : D} [MonObj B]
  [BraidedCategory D] [IsCommMonObj B] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorLeft X)]

section Tensor

variable {F : C ⥤ C} [F.LaxMonoidal] [∀ X Y : C, IsIso (μ F X Y)]
  (σ : A ⟶ F.obj A) [IsMonHom σ] [IsIso σ]
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap σ)]
  (hβF : ∀ X Y : C, μ F X Y ≫ F.map (β_ X Y).hom = (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X)

/-- The structure isomorphism `Φ (L ⊗ K) ≅ Φ L ⊗ Φ K ≅ Φ L ⊗ K ≅ L ⊗ K` of the tensor product of
modules with isomorphisms `sK : Φ K ≅ K` and `sL : Φ L ≅ L`. -/
noncomputable def tensorStrOfIso {K L : Mod C A} (sK : (mapModComap σ).obj K ≅ K)
    (sL : (mapModComap σ).obj L ≅ L) :
    (mapModComap σ).obj ((tensorLeft K).obj L) ≅ (tensorLeft K).obj L :=
  (tensorLeftCompMapModComapIso σ hβF K).app L ≪≫ (tensorLeftMapIso sK).app _ ≪≫
    (tensorLeft K).mapIso sL

/-- The structure isomorphism of the tensor product `L ⊗_A K` of modules with structure
isomorphisms: `Φ (L ⊗ K) ≅ Φ L ⊗ Φ K ≅ Φ L ⊗ K ≅ L ⊗ K`. -/
noncomputable def isoAlgebraTensorStr (K L : IsoAlgebra (mapModComap σ)) :
    (mapModComap σ).obj ((tensorLeft K.carrier).obj L.carrier) ≅
      (tensorLeft K.carrier).obj L.carrier :=
  tensorStrOfIso σ hβF K.str L.str

/-- The tensor product `L ⊗_A K` of modules with structure isomorphisms. -/
noncomputable def isoAlgebraTensorObj (K L : IsoAlgebra (mapModComap σ)) :
    IsoAlgebra (mapModComap σ) :=
  IsoAlgebra.mk ((tensorLeft K.carrier).obj L.carrier) (isoAlgebraTensorStr σ hβF K L)

lemma isoAlgebraTensor_map_comm (K : IsoAlgebra (mapModComap σ))
    {L L' : IsoAlgebra (mapModComap σ)} (f : L ⟶ L') :
    (mapModComap σ).map ((tensorLeft K.carrier).map f.hom.f) ≫
        (isoAlgebraTensorStr σ hβF K L').hom =
      (isoAlgebraTensorStr σ hβF K L).hom ≫ (tensorLeft K.carrier).map f.hom.f := by
  have h₁ : (mapModComap σ).map ((tensorLeft K.carrier).map f.hom.f) ≫
      (tensorLeftCompMapModComapIso σ hβF K.carrier).hom.app L'.carrier =
      (tensorLeftCompMapModComapIso σ hβF K.carrier).hom.app L.carrier ≫
        (tensorLeft ((mapModComap σ).obj K.carrier)).map ((mapModComap σ).map f.hom.f) :=
    (tensorLeftCompMapModComapIso σ hβF K.carrier).hom.naturality f.hom.f
  have h₂ := (tensorLeftMapIso K.str).hom.naturality ((mapModComap σ).map f.hom.f)
  simp only [isoAlgebraTensorStr, tensorStrOfIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  slice_lhs 1 2 => erw [h₁]
  slice_lhs 2 3 => erw [h₂]
  rw [Category.assoc, ← Functor.map_comp]
  rw [← Functor.map_comp]
  exact congrArg (fun x ↦ _ ≫ _ ≫ (tensorLeft K.carrier).map x) f.hom.h

/-- The tensor product `- ⊗_A K` with a module with structure isomorphism, as a functor. -/
noncomputable def isoAlgebraTensor (K : IsoAlgebra (mapModComap σ)) :
    IsoAlgebra (mapModComap σ) ⥤ IsoAlgebra (mapModComap σ) where
  obj L := isoAlgebraTensorObj σ hβF K L
  map f := ObjectProperty.homMk ⟨(tensorLeft K.carrier).map f.hom.f,
    isoAlgebraTensor_map_comm σ hβF K f⟩
  map_id _ := IsoAlgebra.hom_ext ((tensorLeft K.carrier).map_id _)
  map_comp _ _ := IsoAlgebra.hom_ext ((tensorLeft K.carrier).map_comp _ _)

@[simp]
lemma isoAlgebraTensor_obj_carrier (K L : IsoAlgebra (mapModComap σ)) :
    ((isoAlgebraTensor σ hβF K).obj L).carrier = (tensorLeft K.carrier).obj L.carrier :=
  rfl

lemma isoAlgebraTensor_obj_str (K L : IsoAlgebra (mapModComap σ)) :
    ((isoAlgebraTensor σ hβF K).obj L).str = isoAlgebraTensorStr σ hβF K L :=
  IsoAlgebra.mk_str _ _


@[simp]
lemma isoAlgebraTensor_map_hom_f (K : IsoAlgebra (mapModComap σ))
    {L L' : IsoAlgebra (mapModComap σ)} (f : L ⟶ L') :
    ((isoAlgebraTensor σ hβF K).map f).hom.f = (tensorLeft K.carrier).map f.hom.f :=
  rfl

end Tensor

section Exchange

variable {G : C ⥤ D} [G.LaxMonoidal] [∀ X Y : C, IsIso (μ G X Y)]
  (ρ : B ⟶ G.obj A) [IsMonHom ρ] [IsIso ρ]
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap ρ)]
  (hβ : ∀ X Y : C, μ G X Y ≫ G.map (β_ X Y).hom = (β_ (G.obj X) (G.obj Y)).hom ≫ μ G Y X)
  {F : C ⥤ C} [F.LaxMonoidal] [∀ X Y : C, IsIso (μ F X Y)]
  (σ : A ⟶ F.obj A) [IsMonHom σ] [IsIso σ]
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap σ)]
  (hβF : ∀ X Y : C, μ F X Y ≫ F.map (β_ X Y).hom = (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X)
  {F' : D ⥤ D} [F'.LaxMonoidal] [∀ X Y : D, IsIso (μ F' X Y)]
  (σ' : B ⟶ F'.obj B) [IsMonHom σ'] [IsIso σ']
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap σ')]
  (hβF' : ∀ X Y : D, μ F' X Y ≫ F'.map (β_ X Y).hom =
    (β_ (F'.obj X) (F'.obj Y)).hom ≫ μ F' Y X)

/-- The comparison `Γ (L ⊗ K) ≅ Γ L ⊗ Γ K` is compatible with the structure morphisms
`Φ (L ⊗ K) ⟶ L ⊗ K` of tensor products, built from morphisms `sK : Φ K ⟶ K` and `sL : Φ L ⟶ L`,
and with their transports along a lift `E` of a monoidal natural transformation `θ`. -/
lemma tensorLeftCompMapModComapIso_tensorStr_comm (θ : G ⋙ F' ⟶ F ⋙ G)
    [NatTrans.IsMonoidal θ]
    (E : ∀ M : Mod C A, (mapModComap σ').obj ((mapModComap ρ).obj M) ⟶
      (mapModComap ρ).obj ((mapModComap σ).obj M)) (K L : Mod C A)
    (hEK : (E K).hom = θ.app K.X) (hEL : (E L).hom = θ.app L.X)
    (hEKL : (E ((tensorLeft K).obj L)).hom = θ.app ((tensorLeft K).obj L).X)
    (sK : (mapModComap σ).obj K ⟶ K) (sL : (mapModComap σ).obj L ⟶ L) :
    (mapModComap σ').map ((tensorLeftCompMapModComapIso ρ hβ K).hom.app L) ≫
        (tensorLeftCompMapModComapIso σ' hβF' ((mapModComap ρ).obj K)).hom.app
          ((mapModComap ρ).obj L) ≫
        (tensorLeftMap (E K ≫ (mapModComap ρ).map sK)).app _ ≫
        (tensorLeft ((mapModComap ρ).obj K)).map (E L ≫ (mapModComap ρ).map sL) =
      E ((tensorLeft K).obj L) ≫ (mapModComap ρ).map
          ((tensorLeftCompMapModComapIso σ hβF K).hom.app L ≫ (tensorLeftMap sK).app _ ≫
            (tensorLeft K).map sL) ≫
        (tensorLeftCompMapModComapIso ρ hβ K).hom.app L := by
  have hx := tensorLeftCompMapModComapIso_exchange_of_isMonoidal ρ σ σ' hβ hβF hβF' θ
    E L K hEL hEK hEKL
  have n₁ : (tensorLeftMap ((mapModComap ρ).map sK)).app _ ≫
      (tensorLeft ((mapModComap ρ).obj K)).map (E L) =
      (tensorLeft ((mapModComap ρ).obj ((mapModComap σ).obj K))).map (E L) ≫
        (tensorLeftMap ((mapModComap ρ).map sK)).app _ :=
    ((tensorLeftMap ((mapModComap ρ).map sK)).naturality (E L)).symm
  have n₂ := map_tensorLeftMap_app_tensorLeftCompMapModComapIso_hom_app ρ hβ sK
    ((mapModComap σ).obj L)
  have n₃ : (mapModComap ρ).map ((tensorLeft K).map sL) ≫
      (tensorLeftCompMapModComapIso ρ hβ K).hom.app L =
      (tensorLeftCompMapModComapIso ρ hβ K).hom.app ((mapModComap σ).obj L) ≫
        (tensorLeft ((mapModComap ρ).obj K)).map ((mapModComap ρ).map sL) :=
    (tensorLeftCompMapModComapIso ρ hβ K).hom.naturality sL
  rw [tensorLeftMap_comp, NatTrans.comp_app, Functor.map_comp, Functor.map_comp,
    Functor.map_comp]
  simp only [Category.assoc]
  slice_lhs 4 5 => erw [n₁]
  slice_lhs 1 4 => erw [hx]
  slice_lhs 3 4 => erw [← n₂]
  slice_lhs 4 5 => erw [← n₃]

end Exchange

end CategoryTheory.Mod
