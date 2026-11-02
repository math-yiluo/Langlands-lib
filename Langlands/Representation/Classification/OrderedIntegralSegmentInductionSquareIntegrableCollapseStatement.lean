import Langlands.Representation.Classification.SegmentIntegralCoordinates
import Langlands.Representation.Classification.TwoSegmentHeadCommutationStatement
import Langlands.Representation.Classification.Tempered

/-! # Collapse of ordered integral segment induction -/

namespace Langlands.Classification

universe uF uV

/-- Ordered integral segments with the supplied endpoint scalar norms cannot
have more than one factor in an actual induction embedding of a nonzero
square-integrable representation, assuming actual unlinked-head commutation. -/
def OrderedIntegralSegmentInductionSquareIntegrableCollapse
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  TwoSegmentHeadCommutation.{uF,uV} F T →
  ∀ (n : ℕ), 0 < n →
    ∀ (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
      [Nontrivial π],
      T.IsSquareIntegrable π.representation →
      ∀ (d : T.SegmentProductDatum.{max uF uV,uF} n),
        d.HasSegmentHeads →
        SmoothRep.IsSubrepresentation π d.induced →
        ∀ (ρ : T.CuspidalDatum.{max uF uV,uF})
          (a b : Fin d.length → ℤ),
          (∀ i, (d.segments i).HasIntegralCoordinates ρ (b i) (a i)) →
          Monotone a →
          ∀ (t : ℝ) (c : Fin d.length → (F.Carrierˣ →* ℂˣ)),
            (∀ i, HasScalarCharacter (d.blocks i).representation
              GeneralLinear.scalar (c i)) →
            (∀ i (z : F.Carrierˣ), ‖(c i z : ℂ)‖ =
              T.normalizedAbs (z : F.Carrier) ^
                (((d.segments i).degree : ℝ) *
                  (t + ((a i : ℝ) + (b i : ℝ)) / 2))) →
            d.length = 1

end Langlands.Classification
