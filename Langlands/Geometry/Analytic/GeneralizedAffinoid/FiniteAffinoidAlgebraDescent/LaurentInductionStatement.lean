import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology

/-! # Induction along iterated real-radius binary Laurent splits -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

/-- Every nonempty finite full-domain cover of the whole spectrum is refined by a
finite tree of real-radius binary Laurent splits: any property of full domains
that holds on domains inside some cover member, and that holds on a domain as
soon as it holds on both halves `{|a| ≤ ρ}` and `{|a| ≥ ρ}` of some split by an
element `a` of its algebra, holds on the whole domain. -/
def FiniteCoverBinaryLaurentInductionStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (R : PresentedAffinoidAlgebra K) (c : Domain.FiniteCover (Domain.whole K R))
    (P : Domain K R → Prop),
    0 < c.size →
    (∀ U : Domain K R, (∃ i, U.locus ⊆ (c.obj i).locus) → P U) →
    (∀ U : Domain K R, (∃ (a : U.algebra) (ρ : ℝ), 0 < ρ ∧
        ∀ U₁ U₂ : Domain K R,
          U₁.locus = U.spectrumMap '' {y | y a ≤ ρ} →
          U₂.locus = U.spectrumMap '' {y | ρ ≤ y a} → P U₁ ∧ P U₂) → P U) →
    P (Domain.whole K R)

end Langlands.Analytic.PresentedAffinoidAlgebra
