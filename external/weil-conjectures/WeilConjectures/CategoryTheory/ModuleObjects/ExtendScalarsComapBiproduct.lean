/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.Adjunction.MateBiproduct
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

/-!
# Extension followed by restriction of scalars along a finite free morphism

Let `φ : R ⟶ S` be a morphism of commutative algebra objects. By the projection formula,
extension of scalars followed by restriction of scalars is tensoring with `S` regarded as an
`R`-module: `φ^* (S ⊗_R M) ≅ φ^* S ⊗_R M`, naturally in `M`
(`CategoryTheory.Mod.extendScalarsCompComapIso`). If `φ^* S ≅ Rᵈ` is finite free, this is the
biproduct power `M ↦ Mᵈ` (`CategoryTheory.Mod.extendScalarsCompComapIsoBiproductPow`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory

namespace MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Tensoring on the left with isomorphic objects gives isomorphic functors. -/
@[simps!]
def tensorLeftIsoOfIso {X Y : C} (e : X ≅ Y) : tensorLeft X ≅ tensorLeft Y :=
  NatIso.ofComponents (fun Z ↦ whiskerRightIso e Z) fun f ↦ whisker_exchange e.hom f

variable [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C]

/-- Tensoring on the left with the biproduct power `𝟙ᵈ` of the unit is the biproduct power
`X ↦ Xᵈ`. -/
noncomputable def tensorLeftBiproductPowUnitIso (d : ℕ) :
    tensorLeft (⨁ fun _ : Fin d ↦ 𝟙_ C) ≅ Functor.finBiproductPow C d :=
  NatIso.ofComponents (fun X ↦ rightDistributor _ X ≪≫ biproduct.mapIso fun _ ↦ λ_ X)
    fun f ↦ by
      refine biproduct.hom_ext _ _ fun j ↦ ?_
      simp only [curriedTensor_obj_obj, curriedTensor_obj_map, Iso.trans_hom,
        biproduct.mapIso_hom, Category.assoc, biproduct.map_π,
        rightDistributor_hom_comp_biproduct_π_assoc, Functor.finBiproductPow_map,
        biproduct.map_π_assoc]
      rw [whisker_exchange_assoc, leftUnitor_naturality]

end MonoidalCategory

namespace Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- The projection formula map `Q ⊗_R N ⟶ Q ⊗_S (S ⊗_R N)` is natural in the `R`-module `N`. -/
lemma projectionHom_naturality_right (Q : Mod C S) {N N' : Mod C R} (g : N ⟶ N') :
    (comap φ).obj Q ◁ g ≫ projectionHom φ Q N' =
      projectionHom φ Q N ≫ (comap φ).map (Q ◁ (extendScalars φ).map g) := by
  let := comapLaxMonoidal φ
  have hu : g ≫ extendUnit φ N' = extendUnit φ N ≫ (comap φ).map ((extendScalars φ).map g) := by
    rw [← extendRestrictAdjunction_unit_app, ← extendRestrictAdjunction_unit_app]
    exact (extendRestrictAdjunction φ).unit.naturality g
  rw [projectionHom, projectionHom, ← MonoidalCategory.whiskerLeft_comp_assoc, hu,
    MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc]
  exact congrArg (_ ≫ ·)
    (Functor.LaxMonoidal.μ_natural_right (comap φ) Q ((extendScalars φ).map g))

/-- **Extension followed by restriction of scalars** is tensoring with `S` regarded as an
`R`-module: `φ^* (S ⊗_R M) ≅ φ^* S ⊗_R M`, naturally in the `R`-module `M`. -/
noncomputable def extendScalarsCompComapIso :
    extendScalars φ ⋙ comap φ ≅ tensorLeft ((comap φ).obj (regular S)) :=
  NatIso.ofComponents
    (fun N ↦ (comap φ).mapIso (λ_ ((extendScalars φ).obj N)).symm ≪≫
      (projectionIso φ (𝟙_ (Mod C S)) N).symm) fun {N N'} g ↦ by
    simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Category.assoc]
    rw [← Functor.map_comp_assoc, leftUnitor_inv_naturality, Functor.map_comp_assoc]
    refine congrArg (_ ≫ ·) ?_
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, projectionIso_hom, projectionIso_hom,
      ← projectionHom_naturality_right]
    rfl

variable [Abelian C] [MonoidalPreadditive C] [PreservesFiniteColimits (tensorLeft R)]

/-- If `S` is finite free of rank `d` as an `R`-module, extension of scalars along `φ : R ⟶ S`
followed by restriction of scalars is the biproduct power `M ↦ Mᵈ`. -/
noncomputable def extendScalarsCompComapIsoBiproductPow {d : ℕ}
    (e : (comap φ).obj (regular S) ≅ finiteFree R d) :
    extendScalars φ ⋙ comap φ ≅ Functor.finBiproductPow (Mod C R) d :=
  extendScalarsCompComapIso φ ≪≫ tensorLeftIsoOfIso e ≪≫ tensorLeftBiproductPowUnitIso d

end Mod

end CategoryTheory
