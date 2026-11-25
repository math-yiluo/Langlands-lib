# Flat block multipliers and linked pairs with an induction block

Lean module: `Langlands.Representation.Archimedean.RealBlockFlatJacquet`, namespace
`Langlands.Archimedean.RealBlockFlatJacquet`.

This module proves three of the four pair kinds of the Library module
`RealLinkedJacquetPairReduction`. The kinds are IC (an induction block, then a linked character), CI (a
character, then a linked induction block) and the separated case of II (two linked induction
blocks). The rest of II is reduced to the statement
`RealInterlacedInducedInducedLinkedJacquetFunctionalStatement` of the module
`RealInterlacedLinkedJacquetStatement`.

It imports the Library module `RealCharacterCrossing`. From it the proofs use `KF`, `PL`, `frobMap`, `frobMap_rep`, `frobMap_lie`, `frobMap_coe`, `isJacquet_cross`,
`crossExp`, `crossExp_sub`, `sw`, `par`, `par_cases`, `PL_parity`, `blockJacquet_pow_eq_zero` and
`coeff_cos_pow_ne_zero`. From the Library module `RealInductionStagesFourier` (namespace
`Langlands.Archimedean.InductionStages`, opened here) they use `realPositionCharacter_exp`,
`realPosition_of_realInducedBlockAt`, `realInducedFirstCharacter_neg_one`,
`realInducedSecondCharacter_neg_one` and `mem_realStandardModule_of_unitaryCompact`. The last one
says: if `f` is in the principal series of the position characters, and the coefficients
`Φ^{(p)}_k(f)` with `|k| < |m|` vanish on `O(N)` at every induction block of weight `m`, then
`f ∈ realStandardModule N ds`. Everything else also comes from the Library.

## Notation

* `KF n ds` is the space of `O(n)`-finite functions of `realStandardModule n ds`. `π` is
  `realStandardRep n ds` (right translation by `O(n)`) and `realStandardLie n ds` (right
  derivatives).
* `r_p(θ) = blockRotation n p θ` is the rotation in the coordinates `p, p + 1`.
  `Φ^{(p)}_j(f)(g) = blockFourierCoefficient n p j f g = ∫_0^{2π} f(r_p(θ) g) e^{-ijθ} dθ`.
  `coeff j F` is the `j`-th Fourier coefficient of a function `F` of `θ`, and `expMode j θ = e^{ijθ}`.
* `ℓ_μ = blockJacquet n ds p μ`, `ℓ_μ(f) = (2π)⁻¹ Σᶠ_j μ_j Φ^{(p)}_j(f)(1)` (Library,
  `RealBlockJacquetFunctional`).
* `τ_i` are the position exponents, with `χ_i(e^x) = e^{τ_i x}`, and
  `α_i = τ_i + (n - 1)/2 - i`. At a block `p`, `δ = α_p - α_{p+1}`.
* `IsSymmetric ε σ μ` means `μ_{-j} = σ μ_j` for `j ≡ ε (mod 2)`. `IsRecurrent δ ε μ` is the
  recurrence `μ_{j+2}(δ + j) = (j + 2 - δ) μ_j` (Library, `RealBlockMultiplier`).
* `PL τ e` is the list of characters `sgn^{e_i} |·|^{τ_i}`. `frobMap hψ : KF n ds → KF n (PL τ e)`
  is the Frobenius map `v ↦ (g ↦ ψ(π(g) v))` of a real Jacquet functional `ψ` with exponents
  `α` (module `RealCharacterCrossing`).
* `RealLinkedJacquetFunctionalExists n ds` is the conclusion of the pair statements
  (`RealLinkedJacquetPairReduction`).

## Flat multipliers

* `finsum_flat`: the algebra of the tridiagonal formula. Let `c` have bounded support, and let
  `μ_{j+2}(δ + j) = μ_j(δ + j)` and `μ_{j-2}(δ - j) = μ_j(δ - j)` wherever `c_j ≠ 0` ("`μ` is
  flat"). Then the `μ`-sum of the combination
  `(S - δ(x - y)/2 - i v j/2) c_j + (x - y + iv)/4 (δ + j - 2) c_{j-2} + (x - y - iv)/4 (δ - j - 2) c_{j+2}`
  is `S Σᶠ μ_j c_j`. Proof: split the sum into three. Reindex the last two by `j ↦ j ± 2`, and
  compare with `μ_{j±2}(δ ± j) = μ_j(δ ± j)` term by term.

### Section Standard

* `finsum_rightDerivative_flat`: let `μ` be flat for `δ` at the modes `j` with
  `Φ^{(p)}_j(f)(1) ≠ 0` of every `f`. Then for upper triangular `A`,
  `Σᶠ μ_j Φ_j(R_A f)(1) = (Σ_i α_i A_ii) Σᶠ μ_j Φ_j(f)(1)`. This is the Library's
  `blockFourierCoefficient_rightDerivative` followed by `finsum_flat`.
* `isRealJacquetFunctional_blockJacquet_flat`: a flat and symmetric `μ` makes `ℓ_μ` a real
  Jacquet functional with the exponents `α` of `ds`. Its signs `e` satisfy `(-1)^{e_i} = χ_i(-1)`
  off the block and `(-1)^{e_i} = χ_i(-1) σ` on it. The Lie conditions are the previous item
  with `A = X` strictly upper triangular (`S = 0`) and `A = E_ii` (`S = α_i`). The signs are the
  Library's `blockJacquet_hsign`.

A flat multiplier keeps the exponents of `ds` at the block. This differs from the recurrent
multipliers of the Library and of `RealCharacterCrossing`, which exchange them.

## Composites with an intertwiner (section Composite)

* `blockJacquet_comp_ne_zero`: let `B` commute with `O(n)`, and let some `B v` have
  `Φ^{(r)}_j(B v)(1) ≠ 0` with `μ_j ≠ 0`. Then `ℓ_μ ∘ B ≠ 0`. Otherwise the Frobenius function of
  `ℓ_μ` at `B v` vanishes on the rotations `r_r(θ)`. Its `j`-th coefficient is `μ_j Φ_j(B v)(1)`
  (`blockFourierCoefficient_frobFun`, Library), so this coefficient would be `0`.
* `map_pow_lie`: an intertwiner carries `π(Y)^m` to `π(Y)^m`.
* `exists_of_comp`: let `B : KF n ds → KF n (PL τ e)` be a `(𝔤, K)`-intertwiner. Assume
  `τ_r - τ_{r+1} = k > 0` with `k + e_r + e_{r+1}` odd, and that some `B v` has a nonzero
  coefficient `Φ^{(r)}_{par}(B v)(1)` at the parity class `par = e_r + e_{r+1} mod 2`. Then
  `RealLinkedJacquetFunctionalExists n ds` holds. The proof takes the binomial multiplier
  `μ = binomialMultiplier k ε` (Library), `ε = par`. It is recurrent for `τ_r - τ_{r+1} + 1`
  and symmetric, so `isJacquet_cross` makes `ℓ_μ` a real Jacquet functional on `PL τ e`. Its
  exponents are `crossExp`, with `a_r - a_{r+1} = 1 - k`. The functional is `ℓ_μ ∘ B`. It is
  nonzero by `blockJacquet_comp_ne_zero` (`μ_ε ≠ 0`). Its Jacquet conditions transfer along `B`.
  It kills `π(E_{r+1,r})^k` by `blockJacquet_pow_eq_zero`, because the modes `j` with `μ_j ≠ 0`
  satisfy `|j| < k` and `j ≡ k - 1 (mod 2)`.

## The flat engine (section Engine)

* `exists_of_flat`: combine `isRealJacquetFunctional_blockJacquet_flat` at a block `b` with
  `exists_of_comp` for `B = frobMap` at a position `r`. On `O(n)` the Frobenius function of
  `ℓ_μ` is `(frobMap v)(r_r(θ)) = (2π)⁻¹ Σᶠ_j μ_j Φ^{(b)}_j(v)(r_r(θ))` (`frobFun_apply_of_mem`,
  Library). So the nonvanishing condition becomes a nonzero `par`-th Fourier coefficient of
  `θ ↦ Σᶠ_j μ_j Φ^{(b)}_j(v)(r_r(θ))`.
* `isSymmetric_one`: `μ = 1` is symmetric with `σ = 1`. `isSymmetric_sign`: `μ_j = sgn(j)` is
  symmetric with `σ = -1`.
* `flat_sign`: at an induction block of weight `w`, the modes of the module satisfy `|j| ≥ w` and
  `j ≡ w + 1 (mod 2)`, so `|j| ≥ w + 1`. If moreover `δ = w + 1`, then `sgn` is flat:
  `sgn(j ± 2) = sgn(j)` unless `δ ± j = 0`. `μ = 1` is always flat.

## Test vectors (section TestVector)

* `rot_mul_ia`, `rot_mul_ib`, `rot_mul_of_ne`: the rows of `r_b(φ) κ`.
* `zp hb c κ = κ_{b,c} + i κ_{b+1,c}` and `zm hb c κ = κ_{b,c} - i κ_{b+1,c}`. Under `r_b(φ)` they
  are multiplied by `e^{iφ}` and `e^{-iφ}` (`zp_rot`, `zm_rot`, via `expMode_one_eq` and
  `expMode_neg_one_eq`).
* `bf hb c c' m = zp_c^m zp_{c'} + zm_c^m zm_{c'}`. By `bf_rot` it has the two modes `±(m + 1)` along
  `r_b`. The `*_rot_of_disjoint` lemmas say that it is unchanged by the rotations of a disjoint
  block `b'`.
* Two modes: `coeff_two_mode`, `finsum_two_mode`, `finsum_blockFourier_two_mode`. If
  `f(r_b(φ) g) = e^{iNφ} A + e^{-iNφ} B` with `N ≠ 0`, then
  `Σᶠ μ_j Φ_j(f)(g) = 2π(μ_N A + μ_{-N} B)`. `coeff_two_mode_eq_zero`: the coefficients of weight
  `|j| < |N|` vanish.
* Signs: `IsSignEq q F` says `F(diag(s) κ) = (∏ s_i^{q_i}) F(κ)` for sign vectors `s`. It is
  closed under products and powers, holds for matrix entries, and holds for `bf` with
  `q = (m + 1)` at the row `b` (`isSignEq_bf`, by the four sign cases of rows `b, b + 1`).
* `isTranslateFinite_zp`, `isTranslateFinite_zm`, `isTranslateFinite_bf` (from the Library's
  `isTranslateFinite_entry`, `_add`, `_smul`, `_mul`, `_pow`) and the continuity lemmas.

## Test vectors from functions on `O(n)` (section Extension)

* `exists_KF`: let `F` be a continuous function on matrices whose restriction to `O(n)` is
  `O(n)`-finite. Let `F` transform under sign matrices like the position characters
  (`IsSignEq q F` with `(-1)^{q_i} = χ_i(-1)`), and let its coefficients of weight `|k| < |m|`
  along the rotations of each induction block vanish on `O(n)`. Then some `v ∈ KF n ds` equals
  `F` on `O(n)`. Proof: the Library's `principalSeriesExtension` extends `F|_{O(n)}` to the
  principal series. Its sign hypothesis comes from `IsSignEq` and the Library's
  `principalSeriesCharacter_sign`. Membership is `mem_realStandardModule_of_unitaryCompact`.
* `coeff_eq_zero_of_two_mode`: two modes `±N` along `r_p` kill the coefficients of weight
  `|k| < |N|`.
* `exists_of_flat_test`: the assembly. Let `F` be as in `exists_KF` with the two modes `±N` along
  `r_b`, `F(r_b(φ) κ) = e^{iNφ} A(κ) + e^{-iNφ} B(κ)`. Suppose
  `μ_N A(r_r(θ)) + μ_{-N} B(r_r(θ)) = C cos^m θ` with `C ≠ 0`, `m ≤ 2` and `m ≡ par (mod 2)`.
  Then the flat engine applies. The `θ`-function is `2πC cos^m θ`, whose coefficient at
  `m mod 2` is nonzero (`coeff_cos_pow_ne_zero`).

## Linked pairs (section Pairs)

In each case `w = |m|` is the weight of an induction block of exponent `t`. Its positions have
`τ = t ± w/2` and `δ = w + 1`. Its characters at `-1` are `(-1)^{w+1}` and `1`.

* `character_neg_one`, `abs_lt_natAbs_succ`: small facts.
* `linked_induced_character`, `linked_character_induced`, `linked_induced_induced`: unfolding
  `AreRealBlocksUnlinked` and `MoeglinDatum.IsLinked`. The disjunct of the wrong sign contradicts
  the exponent order. What remains is `t(x) - t(z) = (offset) + k` with `k ≥ 1`. The offset is
  `w/2` for IC and CI, and `|w_1 - w_2|/2` for II.
* `realInducedCharacterLinkedJacquetFunctional : RealInducedCharacterLinkedJacquetFunctionalStatement`
  (IC). Here `ds = [induced d, character c]`, `n = 3`, `b = 0`, `r = 1` and `τ_1 - τ_2 = k`. Let
  `ε = c.parity`. The test function is `F = bf(0, c', w) · κ_{22}^ε`. At `r_1(θ)`:
  `zp_0 = zm_0 = 1`, `zp_1 = i cos θ = -zm_1` and `κ_{22} = cos θ`.
  - If `k + ε` is odd: `μ = 1`, `c' = 0`, signs `e = ((w + 1) mod 2, 0, ε)`, giving `2 cos^ε θ`.
  - If `k + ε` is even: `μ = sgn` (flat by `flat_sign`), `c' = 1`. The signs at the block flip,
    `e = (w mod 2, 1, ε)`, giving `2i cos^{1+ε} θ`.
* `realCharacterInducedLinkedJacquetFunctional : RealCharacterInducedLinkedJacquetFunctionalStatement`
  (CI). Here `ds = [character c, induced d]`, `b = 1`, `r = 0` and `τ_0 - τ_1 = k`. The test
  function is `F = bf(2, c', w) · κ_{00}^ε`. At `r_0(θ)`: `zp_2 = i = -zm_2`,
  `zp_1 = zm_1 = cos θ` and `κ_{00} = cos θ`.
  - If `k + ε + w` is even: `μ = 1` and `e = (ε, (w + 1) mod 2, 0)`. Take `c' = 1` for even `w`,
    giving `2i^w cos^{ε+1} θ`, and `c' = 2` for odd `w`, giving `2i^{w+1} cos^ε θ`.
  - If `k + ε + w` is odd: `μ = sgn` and `e = (ε, w mod 2, 1)`. Take `c' = 2` for even `w` and
    `c' = 1` for odd `w`.
* `natAbs_sub_cast`: `|a - b| = a + b - 2 min(a, b)` in `ℂ`.
* `separatedInducedInducedLinkedJacquetFunctional` (II, separated): assume
  `t(d) - t(e) = |w_1 - w_2|/2 + k` with `k > min(w_1, w_2)`. Neither weight needs to be
  nonzero. Here `n = 4`, `b = 0`, `r = 1`, and `τ_1 - τ_2 = v_1 - u_2 = K = k - min(w_1, w_2) > 0`.
  The test function is `F = bf(0, c', w_1) · bf(2, c'', w_2)`. It has the modes `±(w_1 + 1)` along
  `r_0` and `±(w_2 + 1)` along `r_2`, which gives both window conditions. At `r_1(θ)` the second
  factor is `2i^{w_2} cos θ` (`c'' = 2`, `w_2` even) or `2i^{w_2+1}` (`c'' = 3`, `w_2` odd), so its
  power of `cos θ` has parity `w_2 + 1`. The first factor is treated as in IC: `μ = 1`, `c' = 0` if
  `K + w_2` is even, and `μ = sgn`, `c' = 1` if it is odd.
* `realInducedInducedLinkedJacquetFunctional_of_interlaced`: Interlaced implies
  `RealInducedInducedLinkedJacquetFunctionalStatement`. The proof splits on
  `k > min(w_1, w_2)`.

The module compiles with no errors or warnings. The three pair theorems and the reduction use only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The method is internal to the proof of `RealLinkedLanglandsQuotientNotLargeStatement` (the
Langlands quotient of a Langlands-ordered real standard module with a linked pair is not
maximally faithful). It uses the Library's block Fourier coefficients, block
Jacquet functionals and multipliers (`RealBlockJacquetFunctional`, `RealBlockMultiplier`,
`RealBlockLeftDerivative`, `RealBlockFourierPropagation`, `PrincipalSeriesExtension`), the
crossing at a pair of characters (`RealCharacterCrossing`), and the membership lemmas
(`RealInductionStagesFourier`). The case split follows the
cases "discrete series then character", "character then discrete series" and "two discrete series"
(a)/(b) of the Library's `RealLinkedJacquetFunctional.md`. The proofs do not use
intertwining operators: a flat multiplier at the induction block takes their place.
