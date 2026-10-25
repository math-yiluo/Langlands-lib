import Langlands.Representation.RankinSelberg.MultiplicativityStatement

/-!
# Full Whittaker type of normalized upper block induction

The forward preservation assertion derived from JPSS (1983), Sections 2.1 and
2.3, in the actual normalized upper-block convention of
`GammaMultiplicativityStatement`. This is a proposition definition, not a proof.
-/

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uW

/-- Normalized upper block induction preserves full Whittaker type for arbitrary
admissible finite-type block representations, including reducible ones.
The conclusion includes admissibility, finite generation over the group algebra,
and a linear equivalence of the entire Whittaker-functional space with `ℂ`. -/
def NormalizedProductWhittakerTypeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (t k : ℕ) (m : Fin k → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)),
    (∀ i, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t)
        (F.canonicalNormalizedProductInduced (succBlockShape m h) σ))

end Langlands.RankinSelberg
