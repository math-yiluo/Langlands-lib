import Langlands.Automorphic.AdelicHilbertCoordinateActions
import Langlands.Automorphic.CuspidalHilbertFullIntertwiner
import Langlands.Automorphic.CuspidalWhittakerBandSobolevReduction
import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerModel

/-! # Actual multiplicity one from band Sobolev and mixed Whittaker uniqueness -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000

open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Automorphic

open Langlands.Global RankinSelbergGlobal RankinSelbergGlobal.ArchimedeanWhittakerRegularity
  CuspidalFixedSmoothDensity OperatorDeterminantSlice NumberField

universe u

attribute [local instance] regRationalAddCommGroup regContinuousAddCommGroup regSmoothAddCommGroup
  regFormsAddCommGroup regStableAddCommGroup regRealizationAddCommGroup

/-- Whittaker uniqueness for the actual mixed smooth band completions of
unitary-center cuspidal operator realizations. -/
def CuspidalBandMixedWhittakerUniquenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r)
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
    (b : T.realization.UnitaryForm) (hb : ComputesBandInnerProduct T.realization b)
    (ψ : AddChar (Adeles F) ℂ),
    IsStandardAdditiveCharacter F ψ →
    let U := (adelicCompletion T χ hχ hTχ b hb).action
    MixedWhittakerUniqueness (r := r) ψ (finiteHilbertAction F (r + 1) U)
      (infiniteHilbertAction F (r + 1) U) (hilbertCoordinateActions_commute F (r + 1) U)

/-- The exact actual multiplicity-one consequent with the remaining
analytic premises written explicitly. -/
def CuspidalBandMixedMultiplicityOneReductionStatement : Prop :=
  OperatorCompactSobolevStatement.{u} →
  CuspidalBandMixedWhittakerUniquenessStatement.{u} →
    CuspidalOperatorMultiplicityOneStatement.{u}

/-- Mixed Whittaker uniqueness on the actual band completions implies
multiplicity one for the original operator realizations. -/
def CuspidalBandMixedUniquenessReductionStatement : Prop :=
  CuspidalBandMixedWhittakerUniquenessStatement.{u} →
    CuspidalOperatorMultiplicityOneStatement.{u}

end Langlands.Automorphic
