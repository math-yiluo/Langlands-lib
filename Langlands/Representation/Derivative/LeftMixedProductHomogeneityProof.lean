import Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement
import Langlands.Representation.Derivative.LeftMixedProductPhiHatIterate
import Langlands.Representation.Derivative.MirabolicDerivativeUnitInjective
import Langlands.Representation.Derivative.RestrictedProductLevel
import Langlands.Representation.Derivative.MirabolicMinusExactnessProof
import Langlands.Representation.Derivative.LeftMixedProductDerivativeProof

/-!
# Proof of Zelevinsky 5.3: homogeneity of left mixed products

For `τ` homogeneous of level `l > 0`, the unit `τ → Y(τ^(l))` is injective (Ze80 5.1,
(1) ⇒ (3)), so every nonzero subrepresentation of `ρ × τ` has a nonzero derivative of
order `l`. Minus exactness bounds the level of a subrepresentation by the level of `ρ × τ`,
and the published BZ77 4.14(a) theorem bounds the level of `ρ × τ` by `l`.
-/

noncomputable section

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV

/-- Zelevinsky 5.3: a left mixed product `ρ × τ` with homogeneous `τ` is homogeneous. -/
theorem leftMixedProductHomogeneity
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    LeftMixedProductHomogeneity.{uF, uV} F T := by
  let _ := T.topology
  intro ψ k r ρ τ hτ U hU
  have hsub : level T ψ (SmoothRep.subrepresentation ((T.leftMixedProductFunctor k r).obj (ρ, τ)) U)
      ≤ level T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ)) :=
    LevelCalculus.level_le_of_injective T ψ (Mirabolic.minusExactness.{uF, max uF uV} F T)
      (SmoothRep.subtype _ U) (SmoothRep.subtype_injective _ U)
  have htop : level T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ)) ≤ level T ψ τ :=
    RestrictedProductLevel.level_leftMixed_le T ψ
      (leftMixedProductDerivative.{uF, uV} F T) ρ τ
  rcases Nat.eq_zero_or_pos (level T ψ τ) with h0 | hpos
  · omega
  · have hl : 0 < level T ψ τ ∧ level T ψ τ ≤ r + 1 := ⟨hpos, level_le T ψ τ⟩
    have hβ := mirabolicDerivativeOfOrderUnit_injective T ψ r (level T ψ τ) hl τ hτ rfl
    have hlow := le_level_of_hasNonzeroDerivative T ψ _
      (Mirabolic.hasNonzeroDerivative_leftMixed_subrepresentation T ψ hl ρ τ _
        (mirabolicDerivativeOfOrderUnit T ψ r (level T ψ τ) hl τ) hβ U hU)
    omega

end Langlands.Derivative
