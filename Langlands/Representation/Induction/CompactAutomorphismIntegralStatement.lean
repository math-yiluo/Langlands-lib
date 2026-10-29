import Langlands.Representation.Induction.CompactAutomorphism
import Langlands.Representation.Induction.CompactCoinvariantIntegral

/-!
# Automorphism covariance of the compact coinvariant integral

A continuous automorphism `α` of `G` preserving a closed subgroup `H` pulls
compact induction back by precomposition. The statement asserts that the
actual finite-fiber quotient integral into inducing coinvariants is carried,
through the identity-on-vectors transport of coinvariants, to `δH / δG` times
the original integral, naturally in the coefficient representation.
-/

noncomputable section

namespace Langlands.Induction

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

universe uG uV

/-- For a closed subgroup `H` of a Hausdorff locally compact group `G`, supplied
regular two-sided Haar measures on `G` and `H`, every compatible measure `ν` on
`LeftQuotient H`, and every continuous automorphism `α` of `G` preserving `H`:
there is a family of complex linear equivalences
`Coinvariants (automorphismInducing H α hα σ) ≃ₗ[ℂ] Coinvariants σ`, over all
complex representations `σ` of `H` on modules in `Type uV`, sending the class of
each vector to the class of the same vector, natural in every intertwiner, and
carrying the compact coinvariant integral of `f ∘ α` to `δH / δG` times the
compact coinvariant integral of `f`, where `δG` and `δH` are the Haar moduli of
`α` and of its restriction to `H`. -/
def CompactAutomorphismIntegralCovariance : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    (μG : Measure G) (μH : Measure H)
    [IsHaarMeasure μG] [μG.Regular] [IsMulRightInvariant μG]
    [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
    [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
    [BorelSpace (QuotientIntegration.LeftQuotient H)]
    (ν : Measure (QuotientIntegration.LeftQuotient H))
    (hν : QuotientIntegration.IsCompatible H μG μH ν)
    (α : G ≃ₜ* G) (hα : ∀ x : G, α x ∈ H ↔ x ∈ H),
      haveI : LocallyCompactSpace H := hH.locallyCompactSpace
      haveI : IsFiniteMeasureOnCompacts ν := hν.regular.toIsFiniteMeasureOnCompacts
      let δG : ℝ≥0 := mulEquivHaarChar α
      let δH : ℝ≥0 := mulEquivHaarChar (QuotientIntegration.subgroupAutomorphism H α hα)
      let c : ℂ := (((δH / δG : ℝ≥0) : ℝ) : ℂ)
      ∃ A : ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H V),
          Representation.Coinvariants (automorphismInducing H α hα σ) ≃ₗ[ℂ]
            Representation.Coinvariants σ,
        (∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H V) (v : V),
          A σ (Representation.Coinvariants.mk (automorphismInducing H α hα σ) v) =
            Representation.Coinvariants.mk σ v) ∧
        (∀ {V W : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
          (σ : Representation ℂ H V) (τ : Representation ℂ H W) (T : σ.IntertwiningMap τ)
          (z : Representation.Coinvariants (automorphismInducing H α hα σ)),
          A τ (Representation.Coinvariants.map (automorphismInducing H α hα σ)
              (automorphismInducing H α hα τ) (automorphismInducingMap H α hα T) z) =
            Representation.Coinvariants.map σ τ T (A σ z)) ∧
        (∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H V)
          (f : CompactFunctions H σ),
          A σ (compactCoinvariantIntegral H (automorphismInducing H α hα σ) ν
              (precomposeCompactInducedEquiv H α hα σ f)) =
            c • compactCoinvariantIntegral H σ ν f)

end Langlands.Induction
