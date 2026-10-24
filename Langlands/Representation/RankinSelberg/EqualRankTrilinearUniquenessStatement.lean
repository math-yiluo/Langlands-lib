import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# Equal-rank uniqueness of twisted invariant trilinear forms

The proposition of JPSS Section 2.10 is stated on the actual coefficient
models. This module defines its statement and does not prove it.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

/-- JPSS Section 2.10, Proposition: outside finitely many spectral values,
the twisted invariant trilinear forms on the two Whittaker models and row
Schwartz--Bruhat functions have dimension at most one. -/
def EqualRankTrilinearUniquenessStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
      IsOfWhittakerType n (standardCharacter ψ n) π →
      IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
      ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
        let M := (coefficientModel π ℓ).toSubmodule
        let M' := (coefficientModel σ ℓ').toSubmodule
        let S := SchwartzBruhat (Fin (n + 1) → F.Carrier)
        let q := T.residueCardinality
        let abv := normalizedAbsoluteValue T
        let IsTwistedInvariant := fun (s : ℂ) (B : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] ℂ) =>
          ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier)
            (f : M) (f' : M') (Φ Φg : S),
            (∀ x, Φg x = Φ (Matrix.vecMul x g.val)) →
              B (modelRepresentation π ℓ g f) (modelRepresentation σ ℓ' g f') Φg =
                determinantWeight abv g (-s) * B f f' Φ
        ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint q s ∉ E →
          ∀ B B' : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] ℂ,
            IsTwistedInvariant s B → IsTwistedInvariant s B' →
              B ≠ 0 → ∃ c : ℂ, B' = c • B

end Langlands.RankinSelberg
