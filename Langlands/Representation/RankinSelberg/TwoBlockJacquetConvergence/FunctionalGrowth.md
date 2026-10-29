# Uniform geometric growth of character functionals

Module `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.FunctionalGrowth`,
namespace `Langlands.RankinSelberg.TwoBlockConvergence`.

Author: Worker 886.

This is a helper module for the proof of
`Langlands.RankinSelberg.TwoBlockJacquetConvergenceStatement` (JPSS 1983,
Section (4.6)). It proves the uniform growth estimate for the block
functionals `ℓ_i(τ_i(g) v)` that replaces the finite growth exponents of
Whittaker functions used in the source.

## Provenance

The content is internal to this proof. JPSS (source ID
`jpss-1983-rankin-selberg`), Section 2.5 (printed pages 388–389), bound
Whittaker functions through their asymptotic expansion on the torus. This
module does not use Whittaker models, asymptotic expansions or
irreducibility. It applies to every admissible representation that is
finitely generated over the group algebra and to every linear functional `ℓ`
that transforms under the upper unipotent group by a nondegenerate character.
These are exactly the inputs that a full-type block `IsOfWhittakerType` and a
supplied `glInverseFunctionals` element give. The estimate is weaker than the
source's exponents: it allows a geometric growth `C B^e` in the size `e` of
`g`. That suffices for the convergence argument, because the twist `u` can be
taken large.

Here `k` is a field with a valuation; from section `Support` on, `k` is a
nonarchimedean local field. `ϖ` is a uniformizing element
(`Iwasawa.IsUniformizingElement`). `UnequalRankMirabolicUnitTest.levelSet k a`
is the image of `𝔪^a` in `k`.

## Valuation lemmas (section `Valuation`)

- `exists_pow_mul_mem_integer`: every `z` has `ϖ^e z` integral for some `e`.
- `pow_mul_mem_integer_of_le`: if `ϖ^e z` is integral, so is `ϖ^e' z` for `e ≤ e'`.
- `nonneg_of_zpow_mem_integer`, `zpow_mem_integer_of_nonneg`: `ϖ^m` is integral
  iff `m ≥ 0`.
- `uniformizer_mem_maximalIdeal`, `pow_mul_mem_levelSet`: `ϖ^a z ∈ 𝔪^a` for
  integral `z`.

## Size of a matrix (section `Bounded`)

- `IsEntryBounded ϖ e g`: `ϖ^e g` and `ϖ^e g⁻¹` have integral entries.
- `IsEntryBounded.mul`: bounds add under products. `IsEntryBounded.mono`:
  bounds are monotone in `e`. `exists_isEntryBounded`: every `g` has a bound.
  `isEntryBounded_zero_of_mem`: elements of `GL(O)` are bounded by `0`.
- `abs_le_of_isEntryBounded`: if `u ϖ^lam γ` is bounded by `e`, with `u` upper
  unipotent and `γ ∈ GL(O)`, then `|lam_i| ≤ e`. Proof: `u ϖ^lam` is bounded by
  `e`, and its `i`-th diagonal entry and that of its inverse are `ϖ^(lam_i)` and
  `ϖ^(-lam_i)`. So `ϖ^(e ± lam_i)` are integral.

## Support (section `Support`)

`neg_lt_sub_of_ne_zero`: assume `ℓ(ρ(x) v) = χ(∑_i x_(i,i+1)) ℓ(v)` for upper
unipotent `x`, `χ(x₀) ≠ 1` and `ϖ^c₀ x₀` integral. If `w` is fixed by
`K(a)` (`a > 0`) and `ℓ(ρ(ϖ^lam) w) ≠ 0`, then
`lam_i - lam_(i+1) > -(a + c₀)` for all `i`. Proof: if
`d = lam_i - lam_(i+1) ≤ -(a + c₀)`, put `y = ϖ^(-d) x₀ ∈ 𝔪^a` and
`E = 1 + y e_(i,i+1) ∈ K(a)`. This uses the published
`exists_mem_principalLevelSubgroup`. Then `ϖ^lam E ϖ^(-lam)` is upper unipotent
with superdiagonal sum `x₀`. Since `ρ(E) w = w`,
`ℓ(ρ(ϖ^lam) w) = χ(x₀) ℓ(ρ(ϖ^lam) w)`, which forces the value to be `0`.

## Orbits (section `Orbit`)

`finite_integral_orbit`: a smooth vector has finitely many translates under
`GL_(n+1)(O)`. The orbit map is locally constant and `GL_(n+1)(O)` is compact
(`isCompact_integralRange`).

## Growth (section `Growth`)

- `levelSet_anti`: `𝔪^b ⊆ 𝔪^a` for `a ≤ b`.
- `dual_eq_of_mem_principalLevel`: if `χ` is trivial on `𝔪^a₀` and `a ≥ a₀`,
  then `ℓ` is invariant under the upper unipotent elements of `K(a)`, whose
  superdiagonal entries lie in `𝔪^a`.
- `integral_smul_mem_fixedVectors`: `K(a)` is normal in `GL(O)`
  (`conj_mem_rankPrincipalLevel`), so `GL(O)`-translates of `K(a)`-fixed vectors
  are `K(a)`-fixed.

`exists_growth_fixed` (**growth at a fixed level**): let `ρ` be admissible,
`‖χ‖ = 1`, `χ(x₀) ≠ 1`, `ϖ^c₀ x₀` integral, `a > 0`, and `χ` trivial on `𝔪^a`.
Then there is `B ≥ 1` such that every `K(a)`-fixed `w` has a `C` with
`‖ℓ(ρ(g) w)‖ ≤ C B^e` whenever `g` is bounded by `e`. Proof as implemented:

1. Put `r = a + c₀` and `δ = (r·0, r·1, …, r·n)`. Choose `a' ≥ a` with
   `ϖ^(-δ) K(a') ϖ^δ ⊆ K(a)` (`exists_pos_principalLevelOpenSubgroup_subset`).
   Apply `exists_dominant_bound` at level `a'`, which gives a base `B₀`. The
   fixed space is finite-dimensional by admissibility, and `ℓ` is
   `K(a') ∩ N`-invariant by `dual_eq_of_mem_principalLevel`. Take `B = B₀^3`.
2. The vectors `ρ(ϖ^δ) ρ(γ) w`, `γ ∈ GL(O)`, are finitely many
   (`finite_integral_orbit`). So their constants from `exists_dominant_bound`
   have a common upper bound `M`.
3. For `g` bounded by `e`, write `g = u ϖ^lam γ` (`Iwasawa.exists_iwasawa`).
   Then `‖ℓ(ρ(g) w)‖ = ‖ℓ(ρ(ϖ^lam) w')‖` with `w' = ρ(γ) w` fixed by `K(a)`,
   and `|lam_i| ≤ e`. If the value is nonzero, the support lemma makes
   `μ = lam - δ` antitone. Also `ρ(ϖ^δ) w'` is `K(a')`-fixed, and
   `coneWeight μ ≤ 3e + 2rn`. Hence
   `‖ℓ(ρ(ϖ^μ) ρ(ϖ^δ) w')‖ ≤ max M 0 · B₀^(2rn) · (B₀^3)^e`.

`growth_asAlgebraHom`: for a fixed base `B`, the vectors with such a bound form
a submodule over the group algebra. For `r = c·[h]`, use the bound of `g h`,
which is `e + e_h`. Sums are handled by the triangle inequality.

`exists_growth` (**uniform geometric growth**): if moreover `ρ` is finitely
generated over the group algebra and `χ` is trivial on some `𝔪^a₀`, one base
`B ≥ 1` works for every vector `v`. Proof: choose finitely many generators.
By smoothness they are all fixed by one `K(a)` with `a ≥ max(a₀, 1)`. Apply
`exists_growth_fixed` at that level, and extend to the span by
`Submodule.span_induction` and `growth_asAlgebraHom`.
