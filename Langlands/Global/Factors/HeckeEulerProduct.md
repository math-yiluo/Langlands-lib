# Absolute convergence of Hecke Euler products

## Contents

Let `K` be a number field and `χ : HeckeCharacter K` a Hecke character. Here a Hecke character is
a continuous homomorphism from the idele class group `IdeleClasses K` to `ℂˣ`. It need not be
unitary. For a finite place `v` write `topologicalData v` for the published p-adic data of the
completion `K_v` (`Langlands.Global.CompletionPadic.topologicalData`), `ϖ_v` for its uniformizer
unit `LocalFactor.PadicAbelian.uniformizerUnit (topologicalData v)`, `χ_v = χ.finiteComponent v`
and `N(v) = Ideal.absNorm v.asIdeal`. The rank-one local factor
`LocalFactor.PadicAbelian.lFactor (topologicalData v) χ_v s` is `(1 - χ_v(ϖ_v) q_v^{-s})⁻¹` when
the conductor exponent of `χ_v` is `0`, and `1` otherwise.

The module, in namespace `Langlands.Global.HeckeEulerProduct`, proves the following.

- `exists_norm_finiteComponent_uniformizer χ`: there is one real number `β` such that
  `‖χ_v(ϖ_v)‖ = N(v)^(-β)` for every finite place `v`. This holds whether or not `χ_v` is unramified.
- `exists_hasProd_lFactor_subtype χ`: there is a real `σ₀` such that for every set `S` of finite
  places and every `s` with `σ₀ < Re s`, the product of the local factors
  `lFactor (topologicalData v) χ_v s` over `v ∈ S` has a limit `L` in the sense of `HasProd`, and
  `L ≠ 0`. The bound `σ₀` depends only on `χ`, not on `S` or `s`. The proof takes `σ₀ = 1 - β`.
- `exists_hasProd_lFactor χ`: the same statement for the product over all finite places.

Helper results, also public:

- Local bridges between the p-adic data and the completion: `mem_integers_iff` (the valuation
  integers of `topologicalData v` are the closed unit ball), `integersEquiv` (a ring isomorphism
  from these integers to `LocalGalois.baseIntegers (FiniteCompletion K v)`), `residueCardinality_eq`
  (the residue cardinality of `topologicalData v` is `N(v)`), and `norm_uniformizerUnit`
  (`‖ϖ_v‖ = N(v)⁻¹` in the completion).
- `sum_card_absNorm_isBigO` and `summable_absNorm_rpow`: `∑_v N(v)^(-σ)` converges for `σ > 1`,
  the sum running over the finite places.
- `norm_eq_one_of_ideleClass_eq_one`: `‖χ(c)‖ = 1` for every idele class `c` of absolute value `1`.
- `exists_norm_ringHom`, `ray`, `coe_ray`, `ray_add`, `continuous_ray`, `norm_ray` and
  `exists_norm_infiniteComponent_ray`: an archimedean completion `K_w` receives a norm-preserving
  ring map `r` from `ℝ`. Along the ray `t ↦ r(exp t)` of units, `‖χ_w‖` equals `exp (β₀ t)` for
  some real `β₀`.
- `coeff χ v s`: the coefficient `χ_v(ϖ_v) q_v^{-s}` if `χ_v` is unramified, else `0`.
  `lFactor_eq` gives `lFactor = (1 - coeff χ v s)⁻¹`. `norm_spectralVariable` gives
  `‖q_v^{-s}‖ = N(v)^(-Re s)`, and `norm_coeff_le` gives `‖coeff χ v s‖ ≤ N(v)^(-(β + Re s))`.
- `exists_hasProd_inv_one_sub`: if `∑ ‖a i‖` converges and every `‖a i‖ < 1`, then
  `∏ (1 - a i)⁻¹` has a nonzero limit.

## Source and provenance

The classical result for unitary characters is Neukirch, *Algebraic Number Theory* (registered
source `neukirch-1999-algebraic-number-theory`), Chapter VII, §8, Proposition (8.1), printed page
494 (PDF page 505). It says that the Hecke L-series of a character `χ` of the ideal group with
`|χ(𝔭)| ≤ 1` converges absolutely for `Re s ≥ 1 + δ` and equals its Euler product. Neukirch's
proof bounds the logarithm of the Euler product.

This module is internal derived content and takes a different route. It does not assume that
`χ` is unitary. Instead it proves that `|χ_v(ϖ_v)| = N(v)^(-β)` for one `β`, so the half-plane is
`Re s > 1 - β`. This is the familiar fact that a quasi-character of the idele class group is a
unitary character times a real power of the idelic absolute value, here proved only in the form
needed at the uniformizers. The module states only convergence on a half-plane and nonvanishing of
the limit. It does not state uniformity in `s` or analytic continuation.

## Proof

1. **Local bridges.** `mem_integers_iff` compares the valuation of `topologicalData v` with
   Mathlib's adic valuation on the completion. It uses
   `AdelicFunctoriality.valuativeRel_valuation_isEquiv` and the formula for the finite-place norm
   (`FinitePlace.norm_def`, `WithZeroMulInt.toNNReal_le_one_iff`). `integersEquiv` follows from it.
   `residueCardinality_eq` transports the residue field along `integersEquiv`
   (`IsLocalRing.ResidueField.mapEquiv`) and applies `CompletionResidue.card_residueField`.
   `norm_uniformizerUnit` computes the valuation `exp (-1)` of `ϖ_v` from
   `AdelicFunctoriality.FiniteExtension.topologicalData_discreteValuation` and
   `uniformizerUnit_zpow_value`, then converts it to the norm `N(v)⁻¹`.

2. **Summability of `∑ N(v)^(-σ)`.** Mathlib's `Ideal.tendsto_norm_le_div_atTop₀` gives the
   asymptotic `#{I : N(I) ≤ n} / n → residue`. Hence the partial sums of the ideal-counting
   coefficients `a_n = #{I : N(I) = n}` are `O(n)` (`sum_card_absNorm_isBigO`).
   `LSeriesSummable_of_sum_norm_bigO_and_nonneg` then makes `∑ a_n n^(-σ)` summable for `σ > 1`.
   Splitting the ideals into the finite fibres of `absNorm` (`Equiv.sigmaFiberEquiv`,
   `summable_sigma_of_nonneg`) turns this into summability of `N(I)^(-σ)` over the nonzero ideals.
   Restricting along the injection `v ↦ v.asIdeal` gives the sum over the finite places.

3. **Absolute value one on norm-one classes.** The kernel of the idele-class absolute value is
   compact (`NormOneIdeleClass.isCompact_ker_ideleClass`), so `‖χ‖` is bounded there by some `M`.
   If `‖χ(d)‖ > 1` for some `d` in the kernel, its powers would exceed `M`. So `‖χ‖ ≤ 1` on the
   kernel. Applying this to `c` and `c⁻¹` gives `‖χ(c)‖ = 1`.

4. **The exponent.** Fix an infinite place `w`. A norm-preserving map `r : ℝ →+* K_w` comes from
   `ringEquivRealOfIsReal` at a real place and from `ringEquivComplexOfIsComplex` composed with
   `ℝ → ℂ` at a complex place. Isometry of the extension embeddings shows that it preserves norms.
   The function `h t = log ‖χ_w(r(exp t))‖` is continuous and additive, so `h t = t · h 1` by
   `map_real_smul`. Thus `‖χ_w(ray t)‖ = exp (β₀ t)` with `β₀ = h 1`.
   Now let `v` be a finite place and set `t = log N(v) / mult w`. The idele class of `ϖ_v` times
   `ray t` at `w` has absolute value `N(v)⁻¹ · exp (t)^{mult w} = 1`. Here the published formulas
   for the absolute value of the finite and infinite class inclusions are used. By step 3, `χ` has
   absolute value `1` on this class. So `‖χ_v(ϖ_v)‖ = exp (-β₀ t) = N(v)^(-β)` with
   `β = β₀ / mult w`.

5. **The Euler product.** `‖q_v^{-s}‖ = N(v)^(-Re s)` because the residue cardinality is `N(v)`.
   Together with step 4 this gives `‖coeff χ v s‖ ≤ N(v)^(-(β + Re s))`. For `Re s > 1 - β` the
   exponent `β + Re s` exceeds `1`. Step 2 then makes `∑_v ‖coeff χ v s‖` summable, also over any
   subset `S`. Each `‖coeff χ v s‖ < 1` since `N(v) > 1`. Finally
   `multipliable_one_add_of_summable` and `tprod_one_add_ne_zero_of_summable` give a nonzero
   limit of `∏ (1 - coeff)`, and `HasProd.inv₀` inverts it (`exists_hasProd_inv_one_sub`).
   `lFactor_eq` identifies the factors. For all finite places the statement is transported from
   `S = univ` along `Equiv.Set.univ`.
