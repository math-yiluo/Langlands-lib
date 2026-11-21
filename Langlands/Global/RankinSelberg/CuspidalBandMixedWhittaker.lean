import Langlands.Global.RankinSelberg.CuspidalBandMixedSourceData

/-! # Mixed Whittaker functionals on the actual band completions -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000

open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Automorphic Langlands.Automorphic.CuspidalFixedSmoothDensity
  Langlands.Automorphic.OperatorDeterminantSlice NumberField MeasureTheory

universe u

attribute [local instance] regRationalAddCommGroup regContinuousAddCommGroup regSmoothAddCommGroup
  regFormsAddCommGroup regStableAddCommGroup regRealizationAddCommGroup
  finiteAdelicGL_nonarchimedeanGroup

/-- The actual band estimates give Whittaker models on the corresponding
mixed smooth completions, using the canonical maps from the realizations. -/
def CuspidalBandMixedWhittakerModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r)
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
    (b : T.realization.UnitaryForm) (hb : ComputesBandInnerProduct T.realization b)
    (ψ : AddChar (Adeles F) ℂ),
    IsStandardAdditiveCharacter F ψ →
    ∀ (hL2 : ∀ w : T.Space, MemLp (toQuotient F (r + 1) T.realization w) 2
        ((quotientHaarMeasure F (r + 1)).restrict (band F (r + 1)))),
      CuspidalWhittakerBandBound F T hL2 ψ →
      let U := (adelicCompletion T χ hχ hTχ b hb).action
      HasMixedWhittakerModel T ψ (finiteHilbertAction F (r + 1) U)
        (infiniteHilbertAction F (r + 1) U) (hilbertCoordinateActions_commute F (r + 1) U)
        (toHilbertMixed T χ hχ hTχ b hb).toLinearMap

/-- The Whittaker functional on the actual completion evaluates all the
original translated integrals under the given band estimate. -/
theorem hasMixedWhittakerModel_of_bandBound : CuspidalBandMixedWhittakerModelStatement.{u} := by
  intro F _ _ _ r T χ hχ hTχ b hb ψ hψ hL2 hbound
  let U := (adelicCompletion T χ hχ hTχ b hb).action
  exact @hasMixedWhittakerModel_of_smoothSource F _ _ _ r T b.finiteForm.HilbertCompletion
    _ _ _ _ (finiteHilbertAction F (r + 1) U) (infiniteHilbertAction F (r + 1) U)
    (hilbertCoordinateActions_commute F (r + 1) U) ψ hψ hL2 hbound
    (toBandHilbertSmooth T χ hχ hTχ b hb) (toHilbertMixed T χ hχ hTχ b hb).toLinearMap
    (bandSmoothSourceWhittakerData T χ hχ hTχ b hb hL2)

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
