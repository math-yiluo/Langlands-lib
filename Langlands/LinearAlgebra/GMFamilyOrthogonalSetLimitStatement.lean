import Langlands.LinearAlgebra.GMFamilies
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # The limit of `(G, M)`-family integrals along orthogonal sets (Lapid's Lemma 8)

Lapid 2011, §7, Lemma 8 (pp.326–327), in the abstract setting of
`Langlands.LinearAlgebra.GMFamilies`: for a `(G, M)`-family `{d_P}` of Schwartz functions on
`i𝔞_M^*` and the `(G, M)`-family `c_P(λ) = e^{λ(Y_P)}` of a positive `(G, M)`-orthogonal set
`{Y_P}`, the integral of `(cd)_M` over `i(𝔞_M^G)^*` tends to `d_P(0)`, faster than any power of
the distance of `{Y_P}` to the walls. -/

noncomputable section

open scoped RealInnerProductSpace ContDiff
open MeasureTheory

universe u

namespace Langlands.GMFamily

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (R : Finset E) (a : Submodule ℝ E)

/-- A positive `(G, M)`-orthogonal set (Arthur 2005, §17, p.94): points `Y_P ∈ 𝔞_M`,
`P ∈ 𝓟(M)`, such that `Y_P − Y_{P'} = r α^∨` with `r ≥ 0` whenever `P` and `P'` are adjacent
along the simple root `α ∈ Δ_P`; here `α^∨` is replaced by the vector `v` of `a` of the restricted
root, a positive multiple of it. -/
def IsPositiveOrthogonalSet (Y : Finset E → a) : Prop :=
  ∀ S ∈ parabolics R a, ∀ S' ∈ parabolics R a, ∀ v : a, IsAdjacentAlong R a S S' v →
    ∃ r : ℝ, 0 ≤ r ∧ Y S - Y S' = r • v

/-- `𝔞_M^G = 𝔞_M ∩ 𝔞_G^⊥`, the orthogonal complement of `𝔞_G` in `𝔞_M`. -/
def relativeSpace : Submodule ℝ E :=
  a ⊓ (centralSpace R)ᗮ

/-- The point `iΛ_x ∈ i(𝔞_M^G)^* ⊆ i𝔞_M^*` attached to `x ∈ 𝔞_M^G` by the inner product:
`Λ_x(H) = ⟪x, H⟫` for `H ∈ 𝔞_M`. -/
def dualParam (x : relativeSpace R a) : StrongDual ℝ a :=
  innerSL ℝ (Submodule.inclusion inf_le_left x : a)

/-- **Lapid 2011, Lemma 8** (pp.326–327), for positive `(G, M)`-orthogonal sets. Let `R` be
a root set in the Euclidean space `E = 𝔞_0` and `a = 𝔞_M` a Levi space. For every `n` and
`κ` there are finitely many Schwartz seminorms and a constant `C` such that for every
`(G, M)`-family `{d_P}` of Schwartz functions on `i𝔞_M^*`, every `t ≥ 0` and every positive
`(G, M)`-orthogonal set `{Y_P}` with `α(Y_P) ≥ t` for all `P ∈ 𝓟(M)`, `α ∈ Δ_P`, and
`‖Y_P‖ ≤ κ(1 + t)`, and every `P₀ ∈ 𝓟(M)`:
`|∫_{i(𝔞_M^G)^*} ∑_{P ∈ 𝓟(M)} e^{λ(Y_P)} d_P(λ) θ_P(λ)⁻¹ dλ − d_{P₀}(0)|
  ≤ C (1 + t)⁻ⁿ ∑_{P ∈ 𝓟(M)} ‖d_P‖`,
where `‖·‖` is the supremum of the chosen seminorms and `dλ` is the measure on `i(𝔞_M^G)^*`
dual to the Euclidean measure of `𝔞_M^G`: in the coordinates `λ = iΛ_x`, `x ∈ 𝔞_M^G`, it is
`(2π)^{-dim 𝔞_M^G} dx`. -/
def OrthogonalSetLimitStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (R : Finset E) (a : Submodule ℝ E), IsRootSet R → IsLeviSpace R a →
    ∀ (n : ℕ) (κ : ℝ), ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),
      ∀ d : Finset E → SchwartzMap (StrongDual ℝ a) ℂ, IsFamily R a (fun S Λ => d S Λ) →
      ∀ (Y : Finset E → a) (t : ℝ), 0 ≤ t → IsPositiveOrthogonalSet R a Y →
        (∀ S ∈ parabolics R a, ∀ v ∈ simpleRoots a S, t ≤ ⟪v, Y S⟫) →
        (∀ S ∈ parabolics R a, ‖Y S‖ ≤ κ * (1 + t)) →
        ∀ S₀ ∈ parabolics R a,
          ‖((((2 * Real.pi) ^ Module.finrank ℝ (relativeSpace R a))⁻¹ : ℝ) : ℂ) *
              (∫ x : relativeSpace R a,
                cM R a (fun S Λ => Complex.exp (Complex.I * (Λ (Y S) : ℂ)) * d S Λ)
                  (dualParam R a x))
            - d S₀ 0‖ ≤
            C / (1 + t) ^ n *
              ∑ S ∈ parabolics R a, (s.sup (schwartzSeminormFamily ℝ (StrongDual ℝ a) ℂ)) (d S)

end Langlands.GMFamily
