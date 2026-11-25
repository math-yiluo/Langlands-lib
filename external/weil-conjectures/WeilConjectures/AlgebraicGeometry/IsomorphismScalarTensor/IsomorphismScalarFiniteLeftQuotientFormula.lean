/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedModel
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarFiniteComparisonUnit
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarFiniteRightQuotientFormula
import all WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison

/-! # Left finite scalar quotient formula

This is the left half of the finite quotient construction.

## Implementation details

The left half is separated from its right counterpart because the two maps use different
adjunction units and are checked independently on pure tensors.

## References

* Stacks Project, Tags 03EK and 03EL
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.IsomorphismScalarTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- For a normalized completed comparison `b`, there are left completed-to-finite quotient
maps at every level satisfying the pure-tensor formula `LeftQuotientFormula`. -/
theorem left_quotient_formula_exists
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (hb : CompletedFormula l E L ι g b) :
    ∃ vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n,
      LeftQuotientFormula l E L ι g vleft := by
  obtain ⟨bfin, hfin⟩ := finite_formula_unit_exists l E L ι g b hb
  obtain ⟨vright, hright⟩ := right_quotient_formula_exists l E L ι g b hb
  -- Conjugation supplies a natural chain map without a new tensor presentation.
  let e n := Functor.isoWhiskerRight (bfin n) (integralOperationsRestrict l L X n)
  let vleft n := b.hom ≫ vright n ≫ (e n).inv
  refine ⟨vleft, ?_⟩
  intro n P i U s x
  let sX := (inverseImageCompletedCoefficientMap l L g).hom.app (op U) s
  let sfin := (completedIntegralCommRingProjectionUnrestricted l L X n).hom.app (op U) sX
  have hcoef :
      (inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U) sfin =
        (completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app
          (op ((proEtaleIsoPostcompose g).obj U)) s := by
    have hc := congrArg (fun f ↦ (f.hom.app (op U)).hom sX)
      (inverseCoefficient_square l L g n)
    have hs : (inv (inverseImageCompletedCoefficientMap l L g)).hom.app (op U) sX = s :=
      congrArg (fun f ↦ (f.hom.app (op U)).hom s)
        (IsIso.hom_inv_id (inverseImageCompletedCoefficientMap l L g))
    change (completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app
        (op ((proEtaleIsoPostcompose g).obj U))
        ((inv (inverseImageCompletedCoefficientMap l L g)).hom.app (op U) sX) =
      (inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U) sfin at hc
    rw [hs] at hc
    exact hc.symm
  change (((e n).inv.app P).f i).val.app (op U)
    ((((vright n).app P).f i).val.app (op U)
      (((b.hom.app P).f i).val.app (op U)
        (completedScalarTensorSection l E L ι X
          (((inverseComplex l E g).obj P.obj).X i) (op U) sX x))) = _
  rw [hb P i U s x, hright n P i U s x]
  have hh := hfin n P i U sfin x
  simp only [map_one, mul_one, id] at hh
  rw [hcoef] at hh
  have hi := congrArg (fun f ↦ (f.f i).val.app (op U)
    (doublePure l E L ι g n P.obj i U sfin 1 x)) ((e n).hom_inv_id_app P)
  exact (congrArg (fun z ↦ (((e n).inv.app P).f i).val.app (op U) z) hh).symm.trans hi

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
