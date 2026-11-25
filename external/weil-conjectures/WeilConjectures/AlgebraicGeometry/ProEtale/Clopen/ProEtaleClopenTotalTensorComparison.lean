/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenData.ProEtaleClopenTotalTensorKFlatDetectionData

/-! Canonical total tensor comparison for clopen restriction.

## References

* Stacks 0FPQ
-/

@[expose] public noncomputable section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
universe t u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory

namespace AlgebraicGeometry.Scheme.ProEt

/-- Keep the total comparison as a single term, avoiding repeated unfolding of
monoidal sheafification data while checking the normalization clauses. -/
@[irreducible] def clopenTotalComparison
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (ClopenData.clopenTensorRestriction.{t, u} j R).Braided)
    (hcolim : ∀ K : Type (max u (t + 1)), PreservesColimitsOfShape (Discrete K)
      (ClopenData.clopenTensorRestriction.{t, u} j R)) :
    coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
      ClopenData.clopenTensorComplexRestriction.{t, u} j R ≅
      ((ClopenData.clopenTensorComplexRestriction.{t, u} j R).prod
        (ClopenData.clopenTensorComplexRestriction.{t, u} j R)) ⋙
      coefficientTotalTensor.{u, t + 1, t} (topology Y)
        ((ClopenData.clopenTensorRings.{t, u} j).obj R) := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients
    R
  letI := SheafOfModules.monoidalCategory
    R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    R
  letI := SheafOfModules.isMonoidal_W_independentCoefficients
    ((ClopenData.clopenTensorRings.{t, u} j).obj R)
  letI := SheafOfModules.monoidalCategory
    ((ClopenData.clopenTensorRings.{t, u} j).obj R)
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    ((ClopenData.clopenTensorRings.{t, u} j).obj R)
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    ((ClopenData.clopenTensorRings.{t, u} j).obj R)
  let G := ClopenData.clopenTensorRestriction.{t, u} j R
  let : G.Braided := h
  have hsums (n : ℤ) : PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {n})) G := by
    have := hcolim (ULift.{max u (t + 1)}
      (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {n}))
    exact preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  exact Functor.uncurry.mapIso
    (asIso (HomologicalComplex.mapBifunctorComparisonNatTrans
      (Functor.OplaxMonoidal.δNatTrans G) (.up ℤ)))

/-- The canonical total comparison has the expected formula on each summand. -/
theorem clopenTotalComparison_summand
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (ClopenData.clopenTensorRestriction.{t, u} j R).Braided)
    (hcolim : ∀ K : Type (max u (t + 1)), PreservesColimitsOfShape (Discrete K)
      (ClopenData.clopenTensorRestriction.{t, u} j R)) :
    ∀ (P Q : CochainComplex (ClopenData.clopenTensorModules.{t, u} R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      (ClopenData.clopenTensorRestriction.{t, u} j R).map
          (ClopenData.clopenTotalTensorSummand.{t, u} R P Q p q n hpq) ≫
          ((clopenTotalComparison j R h hcolim).hom.app (P, Q)).f n =
        (ClopenData.clopenTensorComparison.{t, u} j R h (P.X p) (Q.X q)).hom ≫
          ClopenData.clopenTotalTensorSummand.{t, u}
            ((ClopenData.clopenTensorRings.{t, u} j).obj R)
            ((ClopenData.clopenTensorComplexRestriction.{t, u} j R).obj P)
            ((ClopenData.clopenTensorComplexRestriction.{t, u} j R).obj Q) p q n hpq := by
  let G := ClopenData.clopenTensorRestriction.{t, u} j R
  let : G.Braided := h
  have hsums (n : ℤ) : PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {n})) G := by
    have := hcolim (ULift.{max u (t + 1)}
      (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {n}))
    exact preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  intro P Q p q n hpq
  unfold clopenTotalComparison
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans G) (.up ℤ) P Q p q n hpq

end AlgebraicGeometry.Scheme.ProEt
