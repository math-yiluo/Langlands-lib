import Langlands.Representation.Archimedean.GeneralLinear
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Continuous Whittaker multiplicity one for unitary archimedean representations

This is the unitary smooth-vector formulation of Shalika (1974), Theorem 3.1,
for the real and complex general linear groups `GL_(n+1)(F)`, `F = ℝ, ℂ`:
two continuous Whittaker functionals on the smooth vectors of a unitary,
topologically irreducible, admissible Hilbert representation are proportional
when the first is nonzero. It is an unproved proposition.
-/

noncomputable section

open scoped Matrix.Norms.Operator InnerProductSpace

namespace Langlands.Archimedean

-- The charts on the units of the matrix algebra, used by `smoothVectors (matrixModel F _)`,
-- need the same transparency setting as `Langlands.Representation.Archimedean.GeneralLinear`.
set_option backward.isDefEq.respectTransparency false

universe u

/-- Continuous unitary Whittaker uniqueness over a specified real or complex
scalar field `F`. For every complex Hilbert space `E : Type u` and every jointly
continuous, inner-product-preserving, topologically irreducible representation
`π` of `GL_(n+1)(F)` on `E` that is admissible for `unitaryCompact F (n + 1)`
(`O(n+1)` or `U(n+1)`), two Whittaker functionals on the smooth vectors for the
standard character `u ↦ ψ(∑ uᵢ,ᵢ₊₁)` of the upper unipotent subgroup are
proportional when the first is nonzero. Continuity of the functionals is the
finite derivative-seminorm bound of `IsContinuousOnSmoothVectors`, not the
Hilbert norm alone. -/
def UnitaryWhittakerMultiplicityOneOver (F : Type) [RCLike F] : Prop :=
  ∀ (n : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (π : Langlands.GeneralLinear (n + 1) F →* (E →L[ℂ] E)),
    IsContinuousRepresentation π →
    (∀ (g : Langlands.GeneralLinear (n + 1) F) (v w : E),
      inner ℂ (π g v) (π g w) = inner ℂ v w) →
    IsTopologicallyIrreducible π →
    IsAdmissible π (unitaryCompact F (n + 1)) →
    ∀ (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter F)
      (ℓ₀ ℓ₁ : smoothVectors (matrixModel F (n + 1)) π →ₗ[ℂ] ℂ),
      IsWhittakerFunctional (matrixModel F (n + 1)) π
        (Langlands.GeneralLinear.upperUnipotent (n + 1) F)
        (Langlands.Whittaker.standardCharacter ψ n) ℓ₀ →
      IsWhittakerFunctional (matrixModel F (n + 1)) π
        (Langlands.GeneralLinear.upperUnipotent (n + 1) F)
        (Langlands.Whittaker.standardCharacter ψ n) ℓ₁ →
      ℓ₀ ≠ 0 → ∃ c : ℂ, ℓ₁ = c • ℓ₀

/-- Shalika's local unitary Whittaker multiplicity one (1974, Theorem 3.1) for both
archimedean fields `ℝ` and `ℂ`, with a free universe `u` for the Hilbert
representation space. -/
def UnitaryWhittakerMultiplicityOneStatement : Prop :=
  UnitaryWhittakerMultiplicityOneOver.{u} ℝ ∧
    UnitaryWhittakerMultiplicityOneOver.{u} ℂ

end Langlands.Archimedean
