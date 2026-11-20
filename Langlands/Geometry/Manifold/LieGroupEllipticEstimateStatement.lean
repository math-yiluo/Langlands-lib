import Langlands.Geometry.Manifold.SmoothGroupDifferential
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Interior estimates for elliptic left-invariant word operators on a Lie group -/

noncomputable section

universe u v

open scoped Manifold ContDiff

set_option autoImplicit false

namespace Langlands.Geometry.Manifold

section Words

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] [ChartedSpace E H] [Group H]
  [LieGroup 𝓘(ℝ, E) ∞ H] {n : ℕ}

/-- The word `[i₁, …, iₖ]` acts by the composite `D_{X i₁} ∘ ⋯ ∘ D_{X iₖ}` of the real tangent
derivatives `groupDirectionalValue` along the positive right orbit; the empty word acts as the
identity. -/
def lieWordDerivative (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H) :
    FreeMonoid (Fin n) →* Function.End (H → ℂ) :=
  FreeMonoid.lift fun i => (groupDirectionalValue 𝓘(ℝ, E) (X i) : (H → ℂ) → H → ℂ)

/-- A finite complex combination of words acts by the same combination of word derivatives. -/
def lieWordAction (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H)
    (P : MonoidAlgebra ℂ (FreeMonoid (Fin n))) (φ : H → ℂ) : H → ℂ :=
  P.coeff.sum fun w c => c • (lieWordDerivative X w : (H → ℂ) → H → ℂ) φ

/-- The commutative evaluation of a word combination at a real covector `ξ` of the identity
tangent space: the word `[i₁, …, iₖ]` goes to `ξ (X i₁) ⋯ ξ (X iₖ)`. On the words of one
fixed length `r` this is the principal symbol at the identity of the corresponding operator. -/
def lieWordSymbol (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H)
    (ξ : GroupLieAlgebra 𝓘(ℝ, E) H →ₗ[ℝ] ℝ) :
    MonoidAlgebra ℂ (FreeMonoid (Fin n)) →ₐ[ℂ] ℂ :=
  MonoidAlgebra.lift ℂ ℂ (FreeMonoid (Fin n)) (FreeMonoid.lift fun i => ((ξ (X i) : ℝ) : ℂ))

end Words

/-- **Interior estimate for elliptic left-invariant operators.** Let `H` be a Lie group modelled
on a finite-dimensional real normed space and let `X i` be finitely many tangent vectors at the
identity. Let `Ptop` be a combination of words of one length `r` whose symbol does not vanish at
any nonzero real covector, and let `Plow` be a combination of shorter words. For every word
combination `Q` there are a compact set `V` and a constant `C ≥ 0` such that every smooth
complex function `φ` with `(Ptop + Plow) φ = 0` on all of `H` satisfies
`‖(Q φ)(1)‖ ≤ C * M` whenever `‖φ‖ ≤ M` on `V`. The set `V` and the constant `C` do not depend
on `φ`. -/
def LieGroupEllipticInteriorEstimateStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Type v) [TopologicalSpace H] [ChartedSpace E H] [Group H]
    [LieGroup 𝓘(ℝ, E) ∞ H] (n r : ℕ) (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H)
    (Ptop Plow : MonoidAlgebra ℂ (FreeMonoid (Fin n))),
    (∀ w ∈ Ptop.coeff.support, w.length = r) →
    (∀ w ∈ Plow.coeff.support, w.length < r) →
    (∀ ξ : GroupLieAlgebra 𝓘(ℝ, E) H →ₗ[ℝ] ℝ, ξ ≠ 0 → lieWordSymbol X ξ Ptop ≠ 0) →
    ∀ Q : MonoidAlgebra ℂ (FreeMonoid (Fin n)),
      ∃ (V : Set H) (C : ℝ), IsCompact V ∧ 0 ≤ C ∧
        ∀ φ : H → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ φ →
          (∀ x : H, lieWordAction X (Ptop + Plow) φ x = 0) →
          ∀ M : ℝ, (∀ x ∈ V, ‖φ x‖ ≤ M) → ‖lieWordAction X Q φ 1‖ ≤ C * M

end Langlands.Geometry.Manifold
