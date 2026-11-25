/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Monoid objects in categories of sheaves

Let `J` be a Grothendieck topology on `C` and `A` a monoidal category, so that `Sheaf J A`
carries the monoidal structure `CategoryTheory.Sheaf.monoidalCategory`, the sheafification of the
objectwise tensor product of presheaves. A monoid structure on the underlying presheaf of a sheaf
`S` induces a monoid structure on `S` (`CategoryTheory.Sheaf.monObjOfPresheaf`), transported from
the sheafification along `sheafify S ≅ S`; its multiplication restricts to the presheaf
multiplication along the comparison `S ⊗ₚ S ⟶ S ⊗ S` (`CategoryTheory.Sheaf.μ_comp_map_mul`).

Morphisms out of a tensor product of sheaves are determined by their restriction along this
comparison (`CategoryTheory.Sheaf.tensor_hom_ext`), so a morphism of sheaves of monoids is a
monoid morphism as soon as its underlying morphism of presheaves is one
(`CategoryTheory.Sheaf.isMonHom_of_isMonHom_map`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {A : Type u₂} [Category.{v₂} A] [MonoidalCategory A] [(J.W (A := A)).IsMonoidal]
  [HasWeakSheafify J A]

attribute [local instance] monoidalCategory

open scoped CategoryTheory.Obj

section

variable (S : Sheaf J A) [MonObj S.obj]

/-- The monoid structure on a sheaf `S` induced by a monoid structure on its underlying presheaf:
the image of the latter under the monoidal sheafification functor, transported along the counit
`sheafify S ≅ S`. -/
@[implicit_reducible]
noncomputable def monObjOfPresheaf : MonObj S :=
  letI : MonObj ((presheafToSheaf J A).obj S.obj) := (presheafToSheaf J A).monObjObj S.obj
  .ofIso (show (presheafToSheaf J A).obj S.obj ≅ S from
    asIso ((sheafificationAdjunction J A).counit.app S))

/-- The multiplication of `CategoryTheory.Sheaf.monObjOfPresheaf` restricts to the presheaf
multiplication along the comparison `S ⊗ₚ S ⟶ S ⊗ S`. -/
lemma μ_comp_map_mul :
    letI := monObjOfPresheaf S
    Functor.LaxMonoidal.μ (sheafToPresheaf J A) S S ≫ (sheafToPresheaf J A).map μ[S] =
      μ[S.obj] := by
  let adj := sheafificationAdjunction J A
  let e : (presheafToSheaf J A).obj S.obj ≅ S := asIso (adj.counit.app S)
  have hμ : Functor.LaxMonoidal.μ (sheafToPresheaf J A) S S = adj.homEquiv _ _
      (δ (presheafToSheaf J A) S.obj S.obj ≫ (e.hom ⊗ₘ e.hom)) := rfl
  have hm : (monObjOfPresheaf S).mul = (e.inv ⊗ₘ e.inv) ≫
      Functor.LaxMonoidal.μ (presheafToSheaf J A) S.obj S.obj ≫ (presheafToSheaf J A).map μ[S.obj] ≫
        e.hom := by
    unfold monObjOfPresheaf
    rw [MonObj.ofIso_mul, Functor.obj.μ_def, Category.assoc]
  have key : (δ (presheafToSheaf J A) S.obj S.obj ≫ (e.hom ⊗ₘ e.hom)) ≫ (e.inv ⊗ₘ e.inv) ≫
      Functor.LaxMonoidal.μ (presheafToSheaf J A) S.obj S.obj ≫ (presheafToSheaf J A).map μ[S.obj] ≫
        e.hom = (presheafToSheaf J A).map μ[S.obj] ≫ e.hom := by
    rw [Category.assoc, tensorHom_comp_tensorHom_assoc, e.hom_inv_id, tensorHom_id,
      id_whiskerRight, Category.id_comp, Functor.Monoidal.δ_μ_assoc]
  change _ ≫ (sheafToPresheaf J A).map (monObjOfPresheaf S).mul = _
  rw [hμ, hm, Adjunction.homEquiv_unit, Category.assoc, ← Functor.map_comp, key,
    Functor.map_comp]
  erw [adj.unit_naturality_assoc, adj.right_triangle_components]
  exact Category.comp_id _

/-- The unit of `CategoryTheory.Sheaf.monObjOfPresheaf` restricts to the presheaf unit along the
comparison `𝟙ₚ ⟶ 𝟙`. -/
lemma ε_comp_map_one :
    letI := monObjOfPresheaf S
    Functor.LaxMonoidal.ε (sheafToPresheaf J A) ≫ (sheafToPresheaf J A).map η[S] = η[S.obj] := by
  let adj := sheafificationAdjunction J A
  have hε : Functor.LaxMonoidal.ε (sheafToPresheaf J A) = adj.homEquiv _ _
      (Functor.OplaxMonoidal.η (presheafToSheaf J A)) := rfl
  have h1 : (monObjOfPresheaf S).one = Functor.LaxMonoidal.ε (presheafToSheaf J A) ≫
      (presheafToSheaf J A).map η[S.obj] ≫ adj.counit.app S :=
    (MonObj.ofIso_one _).trans (Category.assoc _ _ _)
  change _ ≫ (sheafToPresheaf J A).map (monObjOfPresheaf S).one = _
  rw [hε, h1, Adjunction.homEquiv_unit, Category.assoc, ← Functor.map_comp,
    Functor.Monoidal.η_ε_assoc, Functor.map_comp]
  erw [adj.unit_naturality_assoc, adj.right_triangle_components]
  exact Category.comp_id _

end

/-- Morphisms out of the tensor product of two sheaves are determined by their restriction along
the comparison `S ⊗ₚ T ⟶ S ⊗ T` with the presheaf tensor product. -/
lemma tensor_hom_ext {S T U : Sheaf J A} {f g : S ⊗ T ⟶ U}
    (h : Functor.LaxMonoidal.μ (sheafToPresheaf J A) S T ≫ (sheafToPresheaf J A).map f =
      Functor.LaxMonoidal.μ (sheafToPresheaf J A) S T ≫ (sheafToPresheaf J A).map g) : f = g := by
  let adj := sheafificationAdjunction J A
  let φ : (presheafToSheaf J A).obj (S.obj ⊗ T.obj) ⟶ S ⊗ T :=
    δ (presheafToSheaf J A) S.obj T.obj ≫ (adj.counit.app S ⊗ₘ adj.counit.app T)
  have : IsIso φ := by dsimp only [φ]; infer_instance
  have hμ : Functor.LaxMonoidal.μ (sheafToPresheaf J A) S T =
      adj.homEquiv (S.obj ⊗ T.obj) (S ⊗ T) φ :=
    rfl
  rw [hμ] at h
  erw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_right] at h
  exact (cancel_epi φ).1 ((adj.homEquiv _ _).injective h)

/-- Morphisms out of the unit sheaf are determined by their restriction along the comparison
`𝟙ₚ ⟶ 𝟙` with the unit presheaf. -/
lemma unit_hom_ext {U : Sheaf J A} {f g : 𝟙_ (Sheaf J A) ⟶ U}
    (h : Functor.LaxMonoidal.ε (sheafToPresheaf J A) ≫ (sheafToPresheaf J A).map f =
      Functor.LaxMonoidal.ε (sheafToPresheaf J A) ≫ (sheafToPresheaf J A).map g) : f = g := by
  let adj := sheafificationAdjunction J A
  have hε : Functor.LaxMonoidal.ε (sheafToPresheaf J A) =
      adj.homEquiv _ _ (Functor.OplaxMonoidal.η (presheafToSheaf J A)) := rfl
  rw [hε] at h
  erw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_right] at h
  exact (cancel_epi _).1 ((adj.homEquiv _ _).injective h)

/-- A morphism of sheaves of monoids is a monoid morphism if its underlying morphism of
presheaves is one, for the monoid structures induced by the lax monoidal functor
`sheafToPresheaf`. -/
lemma isMonHom_of_isMonHom_map {S T : Sheaf J A} [MonObj S] [MonObj T] (f : S ⟶ T)
    [IsMonHom ((sheafToPresheaf J A).map f)] : IsMonHom f where
  one_hom := unit_hom_ext (by
    rw [Functor.map_comp, ← Category.assoc]
    exact IsMonHom.one_hom (f := (sheafToPresheaf J A).map f))
  mul_hom := tensor_hom_ext (by
    have := IsMonHom.mul_hom (f := (sheafToPresheaf J A).map f)
    simp only [Functor.obj.μ_def, Category.assoc] at this
    rw [Functor.map_comp, Functor.map_comp, this, ← μ_natural_assoc])

end CategoryTheory.Sheaf

namespace CategoryTheory.Functor

open Sheaf

variable {A : Type u₂} [Category.{v₂} A] [MonoidalCategory A] [BraidedCategory A]

attribute [local instance] Sheaf.monoidalCategory

variable {C D E : Type*} [Category C] [Category D] [Category E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] [(K.W (A := A)).IsMonoidal]
  [HasWeakSheafify K A] [(L.W (A := A)).IsMonoidal] [HasWeakSheafify L A]

/-- The identification `G_* ⋙ F_* ≅ FG_*` of pushforwards of sheaves along `F ⋙ G ≅ FG` is a
monoidal natural isomorphism. -/
instance isMonoidal_sheafPushforwardContinuousComp' {F : C ⥤ D} {G : D ⥤ E} {FG : C ⥤ E}
    (e : F ⋙ G ≅ FG) [F.IsContinuous J K] [G.IsContinuous K L] [FG.IsContinuous J L] :
    NatTrans.IsMonoidal (sheafPushforwardContinuousComp' e A J K L).hom where
  unit := by
    rw [ε_sheafPushforwardContinuous_of_iso_comp A J K L e, comp_ε, Category.assoc]
  tensor X Y := by
    apply tensor_hom_ext
    rw [Functor.map_comp, Functor.map_comp, ← μ_natural_assoc]
    ext U
    simpa [sheafPushforwardContinuousComp', sheafPushforwardContinuousComp,
      μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app_assoc,
      μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app] using
      ((Functor.LaxMonoidal.μ (sheafToPresheaf L A) X Y).naturality (e.inv.app U.unop).op).symm

/-- The identification `F_* ≅ 𝟭` of the pushforward along `F ≅ 𝟭` is a monoidal natural
isomorphism. -/
instance isMonoidal_sheafPushforwardContinuousId' {F : C ⥤ C} (e : F ≅ 𝟭 C)
    [F.IsContinuous J J] :
    NatTrans.IsMonoidal (sheafPushforwardContinuousId' e A J).hom where
  unit := by
    rw [ε_sheafPushforwardContinuous_of_iso_id A J e, Iso.inv_hom_id_app]
    rfl
  tensor X Y := by
    apply tensor_hom_ext
    rw [Functor.map_comp, Functor.map_comp, ← μ_natural_assoc]
    ext U
    simpa [sheafPushforwardContinuousId', sheafPushforwardContinuousId,
      μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app_assoc,
      μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app] using
      ((Functor.LaxMonoidal.μ (sheafToPresheaf J A) X Y).naturality (e.inv.app U.unop).op).symm

end CategoryTheory.Functor
