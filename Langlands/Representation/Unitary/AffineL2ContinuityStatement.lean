import Langlands.Representation.Unitary.AffineL2

/-! # Joint continuity of the actual normalized affine L² action: statement -/

open MeasureTheory

namespace Langlands.AffineL2

universe u

/-- Joint continuity of the actual inverse-affine action and actual mirabolic
representation, for every rank and additive Haar measure. -/
def JointContinuity {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ (n : ℕ) [MeasurableSpace (Fin n → F.Carrier)]
    [BorelSpace (Fin n → F.Carrier)]
    (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
    Continuous (fun zf :
        (GeneralLinear n F.Carrier × (Fin n → F.Carrier)) × Lp ℂ 2 μ =>
      operator F T μ zf.1.1 zf.1.2 zf.2) ∧
    Continuous (fun gf : GeneralLinear.mirabolic n F.Carrier × Lp ℂ 2 μ =>
      mirabolicRepresentation F T μ gf.1 gf.2)

end Langlands.AffineL2
