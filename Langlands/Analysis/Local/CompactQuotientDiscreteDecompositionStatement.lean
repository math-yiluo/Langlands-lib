import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Basic

noncomputable section

universe uG

namespace Langlands.QuotientIntegration

open MeasureTheory

/-- On a compact left coset space with a compatible quotient measure, the
original unitary right translation action on `L²` is a Hilbert sum of
topologically irreducible closed invariant subspaces, each isomorphism class
occurring finitely often. -/
def CompactQuotientDiscreteDecompositionStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (_hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [SFinite μH] [μH.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μH]
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    (μG : Measure G) [μG.IsHaarMeasure]
    (ν : Measure (LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
    (_hν : IsCompatible H μG μH ν), CompactSpace (LeftQuotient H) →
    ∀ (π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)),
      (∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y) →
      (∀ x : Lp ℂ 2 ν, Continuous (fun g => π g x)) →
      (∀ (g : G) (φ : Lp ℂ 2 ν),
        (π g φ : LeftQuotient H → ℂ) =ᵐ[ν] fun q => φ (rightTranslate H g q)) →
      ∃ A : Set (Submodule ℂ (Lp ℂ 2 ν)),
        (∀ P ∈ A, P ≠ ⊥ ∧ IsClosed (P : Set (Lp ℂ 2 ν)) ∧
          (∀ (g : G), ∀ x ∈ P, π g x ∈ P) ∧
          ∀ Q : Submodule ℂ (Lp ℂ 2 ν), Q ≤ P → IsClosed (Q : Set (Lp ℂ 2 ν)) →
            (∀ (g : G), ∀ x ∈ Q, π g x ∈ Q) → Q = ⊥ ∨ Q = P) ∧
        IsHilbertSum ℂ (fun P : A => (P.1 : Submodule ℂ (Lp ℂ 2 ν)))
          (fun P => P.1.subtypeₗᵢ) ∧
        ∀ P ∈ A, ∀ hPi : (∀ (g : G), ∀ x ∈ P, π g x ∈ P),
          {Q : Submodule ℂ (Lp ℂ 2 ν) | Q ∈ A ∧ ∃ U : P ≃ₗᵢ[ℂ] Q,
            ∀ (g : G) (x : P), (U ⟨π g x, hPi g x x.2⟩ : Lp ℂ 2 ν) = π g (U x)}.Finite

end Langlands.QuotientIntegration
