import Langlands.Representation.Whittaker.TwoBlockCellIntegrabilityStatement
import Langlands.Representation.Induction.CompactQuotientProof
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Scalar Jacquet integrability for actual compactly supported cell vectors -/

noncomputable section

namespace Langlands.Whittaker

open HarmonicAnalysis MeasureTheory

universe uF uV

/-- Local constancy of smooth induced functions and the defining compact
support of the cell restriction give scalar Jacquet integrability. -/
theorem twoBlockCellJacquetIntegrability :
    TwoBlockCellJacquetIntegrabilityStatement.{uF, uV} := by
  intro p _ F a b V₁ V₂ _ _ _ _ π₁ π₂
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.fieldT2
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.generalLinearTopologicalGroup (a + 1 + (b + 1))
  dsimp only
  intro ψ ℓ μ _ f
  have hpoint : Continuous (twoBlockCellPoint F a b) :=
    continuous_const.mul
      (Shahidi.continuous_intertwiningUnipotent (a + 1) (b + 1) F.Carrier)
  have hlc := (Induction.eval_isLocallyConstant (twoBlockParabolic F a b)
    (twoBlockInducingRepresentation F a b π₁ π₂) f.val).comp ℓ
  have hc : Continuous (fun x => ℓ (twoBlockCellRestriction F a b π₁ π₂ f x)) :=
    (hlc.comp_continuous hpoint).continuous
  have hs : HasCompactSupport (fun x => ℓ (twoBlockCellRestriction F a b π₁ π₂ f x)) :=
    (hasCompactSupport_twoBlockCellRestriction F a b π₁ π₂ f).comp_left (map_zero ℓ)
  exact ((Shahidi.continuous_intertwiningJacquetKernel a b ψ).mul hc).integrable_of_hasCompactSupport
    hs.mul_left

end Langlands.Whittaker
