import Langlands.Representation.Classification.SegmentIntegralCoordinates

/-! # Scalar norms of strong heads on an integral cuspidal line -/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- One real parameter on a cuspidal line gives the scalar norm of every
actual strong segment head on every integral interval of that line. -/
def IntegralSegmentHeadScalarNorm : Prop :=
  letI := T.topology
  ∀ ρ : T.CuspidalDatum.{max uF uV, uF},
    ∃ t : ℝ, ∀ (Δ : T.Segment.{max uF uV, uF}) (b a : ℤ),
      Δ.HasIntegralCoordinates ρ b a →
      ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier),
        T.IsSegmentHead Δ π →
        ∃ c : F.Carrierˣ →* ℂˣ,
          HasScalarCharacter π.representation GeneralLinear.scalar c ∧
            ∀ z : F.Carrierˣ, ‖(c z : ℂ)‖ =
              T.normalizedAbs z ^ ((Δ.degree : ℝ) *
                (t + ((a : ℝ) + (b : ℝ)) / 2))

end Langlands.Classification
