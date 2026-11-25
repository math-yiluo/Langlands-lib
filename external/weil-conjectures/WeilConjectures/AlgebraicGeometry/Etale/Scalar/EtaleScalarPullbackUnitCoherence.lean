/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorCoherence
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientLeftUnitCoherence
import WeilConjectures.CategoryTheory.SmoothPurity.CompositeLeftUnitCoherence
import WeilConjectures.CategoryTheory.Tensor.TensorIsoUnitCoherence

/-! # The coefficient unit is preserved by the normalized scalar/pullback square -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem tensor_naturality_left
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (S : C ⥤ D)
    (d : Functor.uncurry.obj (curriedTensor C) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (curriedTensor D))
    {P Q : C} (a : P ⟶ Q) (M : C) :
    S.map (a ▷ M) ≫ d.hom.app (Q, M) =
      d.hom.app (P, M) ≫ S.map a ▷ S.obj M := by
  have h := d.hom.naturality (show (P, M) ⟶ (Q, M) from (a, 𝟙 M))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  change S.map (a ▷ M ≫ Q ◁ 𝟙 M) ≫ d.hom.app (Q, M) = _ at h
  simp only [whiskerLeft_id, Category.comp_id] at h
  change S.map (a ▷ M) ≫ d.hom.app (Q, M) =
    d.hom.app (P, M) ≫ S.map a ▷ S.obj M ≫ S.obj Q ◁ S.map (𝟙 M) at h
  rw [S.map_id, whiskerLeft_id, Category.comp_id] at h
  exact h

/-- Unit compatibility follows from tensor compatibility and the two left-unit laws.
Source: Stacks 07A4 and 0G7E
(blueprint: lem-pur-etale-scalar-pullback-unit-coherence).
Proof: the composite tensor comparisons on Q followed by pullback and on pullback
followed by Q both satisfy left unitality by pasting the constituent left-unit
laws. The scalar/pullback tensor square identifies these two tensor comparisons.
An invertible tensor-compatible natural transformation between these unital
functors preserves the unit, by tensorIso_preserves_unit. Its unit equation is
exactly the displayed formula. -/
theorem etaleScalarPullback_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (scalarPullbackIso φ f).hom.app (𝟙_ (DerivedCategoryModule A Y)) ≫
      (scalarExtension φ X).map (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom ≫
      (ExceptionalCoefficients.unitIso φ X).hom =
    (upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.map
        (ExceptionalCoefficients.unitIso φ Y).hom ≫
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} B) f).hom := by
  let S := scalarExtension φ Y
  let S' := scalarExtension φ X
  let L := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
  let L' := (upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor
  let dS := ExceptionalCoefficients.tensorIso φ Y
  let dS' := ExceptionalCoefficients.tensorIso φ X
  let dL := leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f
  let dL' := leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} B) f
  let eS := ExceptionalCoefficients.unitIso φ Y
  let eS' := ExceptionalCoefficients.unitIso φ X
  let eL := leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f
  let eL' := leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} B) f
  let dF (P Q : DerivedCategoryModule A Y) :=
    L'.mapIso (dS.app (P, Q)) ≪≫ dL' (S.obj P) (S.obj Q)
  let dG (P Q : DerivedCategoryModule A Y) :=
    S'.mapIso (dL P Q) ≪≫ dS'.app (L.obj P, L.obj Q)
  apply tensorIso_preserves_unit (S ⋙ L') (L ⋙ S') (scalarPullbackIso φ f)
    dF dG (L'.mapIso eS ≪≫ eL') (S'.mapIso eL ≪≫ eS')
  · intro P
    simp only [dF, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    apply composite_left_unit S L' (fun P Q ↦ dS.app (P, Q)) dL' _ eS eL'
      (ExceptionalCoefficients.tensorIso_left_unit φ Y)
      (leftDerivedUpperStarTensorComparison_leftUnitor_hom (ModuleCat.{u + 1} B) f) P
    intro P Q a M
    exact leftDerivedUpperStarTensorIso_hom_naturality_left f a M
  · intro P
    simp only [dG, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    apply composite_left_unit L S' dL (fun P Q ↦ dS'.app (P, Q)) _ eL eS'
      (leftDerivedUpperStarTensorComparison_leftUnitor_hom (ModuleCat.{u + 1} A) f)
      (ExceptionalCoefficients.tensorIso_left_unit φ X) P
    intro P Q a M
    exact tensor_naturality_left S' dS' a M
  · intro P Q
    simpa only [dF, dG, S, S', L, L', dS, dS', dL, dL',
      Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
      derivedTensor, curriedTensor_obj_obj, Category.assoc] using
      (etaleScalarPullback_tensor φ f P Q)

end AlgebraicGeometry.Etale
