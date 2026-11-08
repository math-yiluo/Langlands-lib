# Brauer relations among small twists of a highly ramified norm pullback

Author: Worker 1838. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. It is the
local half of Deligne's Lemma 4.16, used in the global argument at ramified places
other than the distinguished one. After a global twist by a character `α` that is
highly ramified there, every generator character of the localized relation has the
form `χ₀ · (α ∘ N)` with `χ₀` of bounded conductor. The relation-level statement is
`exists_bound_evaluationMap_eq_zero_of_ramified_normPullback`. The general kernel
statement is not claimed.

It builds on `BrauerKernel.LinearTwist` (the same candidate) and the accepted units
`BrauerKernel.Determinant` (`characterRatioMap_eq_zero`) and
`BrauerKernel.UnramifiedExponent` (`normPullback`, `normPullback_apply`).

## Standalone facts (`Langlands.PadicField.TopologicalData`)

Here `F → E` is a finite extension of p-adic fields compatible with `Padic p`, with
arbitrary topological data `T`, `S`.

- `ord_algebraMap_eq_mul`: for `ϖ` with `T.ord ϖ = 1`,
  `S.ord (i x) = S.ord (i ϖ) · T.ord x`. This follows from the published
  `LocalClassField.ramificationIndex_mul_ord_relative_algebraMap`, applied to `x` and to
  `ϖ`, after cancelling `e_F`.
- `ord_algebraMap_pos`: `0 < S.ord (i ϖ)`. By the same identity,
  `e_F · S.ord (i ϖ) = e_E`.
- `additiveConductor_traceCharacter_lt`: if `Tr_{E/F} x₀ = 1`, then
  `n(ψ ∘ Tr) < S.ord (i ϖ) · (n(ψ) + 1) - S.ord x₀`. Take `w` of order at least
  `-(n(ψ) + 1)` with `ψ(w) ≠ 1`. Then `x = i(w) x₀` has trace `w`, and its order puts
  it in the lattice of the displayed level. So `ψ ∘ Tr` is not trivial there.
- `normPullback_linearization`: suppose `α(z) = ψ(c (z - 1))` on `U_F^n`, and
  `β(x) = α(N x)` for all `x`. Let `a ∈ O_F` be nonzero with `v(a) < 1`,
  `v(a) ≤ exp(-n)` and `v(c) v(a)^2 ≤ exp(n(ψ))`. Let `m₀ > 0` with
  `S.ord (i a) ≤ m₀`. Then `β(1 + x) = (ψ ∘ Tr)(i(c) x)` for every `x` of order at least
  `m₀`. Write `x = i(a) y` with `y` integral. The published `padicDeepUnitNormTrace`
  gives `α(N(1 + i(a) y)) = ψ(c a Tr y)`, and `Tr(i(c a) y) = c a Tr y` by `F`-linearity.

## Common closure (`Langlands.LocalFactor.NonabelianBrauer`)

- `IsHalfLinearizer F E ψ α c` (definition): the unit `c ∈ E^×` has the exact order
  `-(a(α) + n(ψ))`, and `α(z) = ψ(c (z - 1))` for every `z ∈ U_E^(a(α) - ⌊a(α)/2⌋)`.
  This is Deligne's element `γ` of Lemma 4.16, at the half level used by the published
  rank-one stability proof.
- `exists_isHalfLinearizer`: every `α` with `a(α) ≥ 2` has one. This is the published
  `exists_deep_linearization` at level `m = a(α) - ⌊a(α)/2⌋`, with its lattice form
  `α(1 + x) = ψ(c x)` rewritten on principal units.
- `generatorValue_of_twistFactor` and `evaluationMap_eq_zero_of_twistFactor`: fix
  `γ ∈ E^×`. Suppose every generator `g = (L, χ, χ')` in the support of an actual
  relation (`presentationMap F e E z = 0`, normalized family) has `χ = χ₀ β` and
  `χ' = χ₀' β`. Suppose also that its epsilon expressions satisfy
  `ε(χ₀ β) = χ₀(γ) ε(β)` and `ε(χ₀' β) = χ₀'(γ) ε(β)`, for `ψ ∘ Tr_{L/E}` and the
  supplied Haar measure of `L`. Then each generator value is the character ratio
  `χ(γ) / χ'(γ)`, so the evaluation equals `characterRatioMap F E γ z`. That vanishes
  by the accepted `characterRatioMap_eq_zero`.
- `exists_bound_abelianEpsilonExpression_twist`: fix `E ⊆ L`, `ψ` on `E` and `K`.
  There is `B` with the following property. Suppose `a(α) ≥ B` and
  `IsHalfLinearizer F E ψ α c`. Then for every `χ₀` on `L` with `a(χ₀) ≤ K` and every Haar measure `μ` on `L`:
  `ε(χ₀ · normPullback α, ψ ∘ Tr, μ) = χ₀(c)⁻¹ · ε(normPullback α, ψ ∘ Tr, μ)`.
  The proof chooses `x₀` with `Tr x₀ = 1` (`Algebra.trace_surjective`), sets
  `B = 2 (K + max(0, -ord x₀) + 2)`, and puts `m_E = a(α) - ⌊a(α)/2⌋` and
  `a = ϖ^(m_E)` for the uniformizer `ϖ` of `E`. The preceding facts linearize
  `α ∘ N` by `c` on the lattice of level `r m_E` of `L`, with `r = ord_L(ϖ)`. They
  also bound `n(ψ ∘ Tr)` above. Integer arithmetic (`nlinarith`, using `r ≥ 1`) then
  checks the two size conditions of `abelianEpsilonExpression_mul_of_linearization`,
  applied with `K + 1`.
- `exists_bound_evaluationMap_eq_zero_of_ramified_normPullback`: fix a finite set
  `Ls` of fields and a bound `K`. There is `B` with the following property. Let
  `a(α) ≥ B`, and let `z` be an actual relation (normalized family). Suppose every
  generator `g` of its support has `g.extension ∈ Ls`, and characters
  `χ₀ · normPullback α` and `χ₀' · normPullback α` with `a(χ₀), a(χ₀') ≤ K`. Then
  `evaluationMap F E ψ measures z = 0`. Here `B` is the maximum of `2` and the bounds
  of the previous item over `Ls`. `exists_isHalfLinearizer` supplies `c` for `α`,
  independently of the generator. The previous item gives the twist
  factors with `γ = c⁻¹`, and `evaluationMap_eq_zero_of_twistFactor` concludes.

The field universe `uF` and the representation universe `uV` are independent. The
bound `B` depends only on `E`, `ψ`, `Ls` and `K`, never on `α` or `z`. That is the
order of choices in Deligne's argument, where `α` is chosen after the relation.

## Provenance

Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973),
registered as `deligne-1973-local-constants`, SHA256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`, Lemma 4.16 and its
proof (printed pages 545–547, PDF pages 45–47). Deligne uses one element `γ`
linearizing `α`, the identity `ε(χα, ψ) = χ(γ)^{-1} ε(α, ψ)` (4.16.1), the norm
expansion (4.16.2), and the conductor of `α ∘ N_{L/K}` up to `O(1)`. Here the
`O(1)` bookkeeping is replaced by the explicit trace-one bound above, and the exact
conductor of `α ∘ N` is never computed; only a lower bound is used. The statement is
phrased in the common-closure presentation, so it feeds the Brauer-relation kernel
identity directly instead of Deligne's `α`-theory of constants.
