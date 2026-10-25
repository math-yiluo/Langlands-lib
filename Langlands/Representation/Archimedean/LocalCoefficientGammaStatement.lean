import Langlands.Representation.Archimedean.Induction
import Langlands.Representation.Archimedean.StandardModule
import Langlands.Weil.Representation.SumsTensor
import Langlands.Weil.Representation.Dual

/-!
# Shahidi's local coefficients for `GL_{m+1} × GL_{n+1}` over `ℝ` and `ℂ`

Shahidi 1985, Theorems 3.1 and 3.13, for the maximal parabolic subgroup of type
`(m+1, n+1)` of `GL_{m+n+2}`. The representation `σ` of the Levi subgroup is an irreducible
admissible generic Banach representation with standard-module parameter `(φ₁, φ₂)`. The local
coefficient of the Library's archimedean induced representations is `z^(m+1)` times the
gamma factor `γ(s, φ₁ ⊗ φ₂^∨, ψ)`, where `z` is the scalar of `σ(1, -1)`. The gamma factor uses
any block presentations of the actual Weil representations `φ₁ ⊗ φ₂^∨` and `φ₂ ⊗ φ₁^∨`, the
character `ψ_a` and its self-dual Haar measure, which is also the measure of all three
integrals. The relation is stated in multiplied form for `Re s` large. Nothing is proved.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator NNReal

namespace Langlands.Archimedean

open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean

-- As in `GeneralLinear`: the charts on units need reduction through the normed-ring
-- instances of matrices.
set_option backward.isDefEq.respectTransparency false

universe uE

/-- Shahidi's Theorem 3.1 for `GL_{m+1}(ℝ) × GL_{n+1}(ℝ)`. Let `ψ(x) = e^{2πiax}`, with
self-dual Haar measure `μ = |a|^{1/2} dx`, and let `σ` be an irreducible admissible
`ψ`-generic Banach representation with standard-module parameter `(ds₁, ds₂)`, so that
`φᵢ = realModel dsᵢ`, and with `σ(1, -1) = z`. Then there is `b` such that for all `Re s > b`,
every `ψ`-Whittaker functional `ℓ` of `σ`, the same functional `ℓ'` on `σ̃`, block lists `P`
and `Q` presenting `φ₁ ⊗ φ₂^∨` and `φ₂ ⊗ φ₁^∨`, and every section `f` of `I(s, σ)`:
`L(1-s, Q)⁻¹ λ(f) = z^(m+1) ε(s, P, ψ, μ) L(s, P)⁻¹ λ'(A f)`, all integrals for `μ`. -/
def RealLocalCoefficientGammaStatement : Prop :=
  ∀ (m n : ℕ) (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (σ : Langlands.GeneralLinear (m + 1) ℝ × Langlands.GeneralLinear (n + 1) ℝ →*
      (E →L[ℂ] E))
    (a : ℝˣ) (ds₁ ds₂ : List RealBlock) (z : ℂ),
    IsGenericBanachPairRepresentation ℝ (realScaledCharacter a) m n σ →
    HasRealPairParameter σ ds₁ ds₂ →
    σ (1, -1) = z • ContinuousLinearMap.id ℂ E →
    ∃ b : ℝ, ∀ (ℓ : smoothVectors (pairModel ℝ (m + 1) (n + 1)) σ →ₗ[ℂ] ℂ)
      (ℓ' : smoothVectors (pairModel ℝ (n + 1) (m + 1)) (exchange ℝ (m + 1) (n + 1) σ) →ₗ[ℂ]
        ℂ),
      IsWhittakerFunctional (pairModel ℝ (m + 1) (n + 1)) σ (pairUnipotent ℝ (m + 1) (n + 1))
        (pairCharacter ℝ (realScaledCharacter a) m n) ℓ →
      (∀ (v : E) (hv : v ∈ smoothVectors (pairModel ℝ (m + 1) (n + 1)) σ)
        (hv' : v ∈ smoothVectors (pairModel ℝ (n + 1) (m + 1)) (exchange ℝ (m + 1) (n + 1) σ)),
        ℓ' ⟨v, hv'⟩ = ℓ ⟨v, hv⟩) →
      ∀ P Q : List RealBlock,
      Nonempty (FiniteRepresentation.Equiv (realModel P).val
        (FiniteRepresentation.tensor (realModel ds₁).val
          (FiniteRepresentation.dual (realModel ds₂).val))) →
      Nonempty (FiniteRepresentation.Equiv (realModel Q).val
        (FiniteRepresentation.tensor (realModel ds₂).val
          (FiniteRepresentation.dual (realModel ds₁).val))) →
      ∀ s : ℂ, b < s.re → ∀ f : sourceSpace ℝ (m + 1) (n + 1) σ s,
        SatisfiesLocalCoefficientRelation ℝ
          (realScaledMeasure (NNReal.sqrt ‖(a : ℝ)‖₊)
            (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)))
          m n s (realScaledCharacter a) σ ℓ ℓ' f
          ((realLFactor Q).denominator (1 - s))
          (z ^ (m + 1) *
            (realEpsilon P a (NNReal.sqrt ‖(a : ℝ)‖₊)
              (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ) *
            (realLFactor P).denominator s)

/-- Shahidi's Theorem 3.13 for `GL_{m+1}(ℂ) × GL_{n+1}(ℂ)`. Let `ψ(z) = e^{2πi tr(az)}`, with
self-dual Haar measure `μ = |a|_ℂ^{1/2} · 2 dx dy`, and let `σ` be an irreducible admissible
`ψ`-generic Banach representation with standard-module parameter `(ds₁, ds₂)` of complex
characters and `σ(1, -1) = z`. Then, as in the real case, for `Re s` large,
`L(1-s, Q)⁻¹ λ(f) = z^(m+1) ε(s, P, ψ, μ) L(s, P)⁻¹ λ'(A f)` for block lists `P` and `Q`
presenting `φ₁ ⊗ φ₂^∨` and `φ₂ ⊗ φ₁^∨` over the complex Weil group `ℂˣ`. -/
def ComplexLocalCoefficientGammaStatement : Prop :=
  ∀ (m n : ℕ) (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (σ : Langlands.GeneralLinear (m + 1) ℂ × Langlands.GeneralLinear (n + 1) ℂ →*
      (E →L[ℂ] E))
    (a : ℂˣ) (ds₁ ds₂ : List ComplexCharacterData) (z : ℂ),
    IsGenericBanachPairRepresentation ℂ (complexScaledCharacter a) m n σ →
    HasComplexPairParameter σ ds₁ ds₂ →
    σ (1, -1) = z • ContinuousLinearMap.id ℂ E →
    ∃ b : ℝ, ∀ (ℓ : smoothVectors (pairModel ℂ (m + 1) (n + 1)) σ →ₗ[ℂ] ℂ)
      (ℓ' : smoothVectors (pairModel ℂ (n + 1) (m + 1)) (exchange ℂ (m + 1) (n + 1) σ) →ₗ[ℂ]
        ℂ),
      IsWhittakerFunctional (pairModel ℂ (m + 1) (n + 1)) σ (pairUnipotent ℂ (m + 1) (n + 1))
        (pairCharacter ℂ (complexScaledCharacter a) m n) ℓ →
      (∀ (v : E) (hv : v ∈ smoothVectors (pairModel ℂ (m + 1) (n + 1)) σ)
        (hv' : v ∈ smoothVectors (pairModel ℂ (n + 1) (m + 1)) (exchange ℂ (m + 1) (n + 1) σ)),
        ℓ' ⟨v, hv'⟩ = ℓ ⟨v, hv⟩) →
      ∀ P Q : List ComplexCharacterData,
      Nonempty (FiniteRepresentation.Equiv (complexModel P).val
        (FiniteRepresentation.tensor (complexModel ds₁).val
          (FiniteRepresentation.dual (complexModel ds₂).val))) →
      Nonempty (FiniteRepresentation.Equiv (complexModel Q).val
        (FiniteRepresentation.tensor (complexModel ds₂).val
          (FiniteRepresentation.dual (complexModel ds₁).val))) →
      ∀ s : ℂ, b < s.re → ∀ f : sourceSpace ℂ (m + 1) (n + 1) σ s,
        SatisfiesLocalCoefficientRelation ℂ
          (complexScaledMeasure ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero))
          m n s (complexScaledCharacter a) σ ℓ ℓ' f
          ((complexLFactor Q).denominator (1 - s))
          (z ^ (m + 1) *
            (complexEpsilon P a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) *
            (complexLFactor P).denominator s)

/-- Shahidi's Theorems 3.1 and 3.13 for `GL_{m+1} × GL_{n+1}`: the real and the complex
comparison of the local coefficient with `z^(m+1) γ(s, φ₁ ⊗ φ₂^∨, ψ)`. -/
def LocalCoefficientGammaStatement : Prop :=
  RealLocalCoefficientGammaStatement.{uE} ∧ ComplexLocalCoefficientGammaStatement.{uE}

end Langlands.Archimedean
