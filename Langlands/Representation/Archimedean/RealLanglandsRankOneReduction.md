# Reduction of the real Langlands classification to a rank-one step

Worker 63 wrote this module for Task 6747 (`505270a8-39b1-487d-afdb-01f552e4ab3b`). That task's
target is the Library's `Langlands.Archimedean.RealLanglandsFromPrincipalSeriesStatement`
(module `Langlands.Representation.Archimedean.RealLanglandsQuotientReduction`). The target says:
if an irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module `(ρ, π)` receives a nonzero intertwiner
from the `O(n)`-finite principal series of `n` characters of `ℝ^×`, in any order, then it
receives a nonzero intertwiner from the standard module of a list of real blocks of total rank
`n` in Langlands order.

This module states one local claim, `RealRankOneStepStatement`, about two adjacent blocks in
the wrong order. It proves that the claim implies the target
(`realLanglandsFromPrincipalSeries_of_rankOneStep`). The proof sorts the blocks one adjacent
step at a time. The combinatorics are proved in full; the representation theory is all in the
rank-one claim.

All declarations are in the namespace `Langlands.Archimedean`. The Library's `RealBlock`,
`realRank`, `RealCharacterData` and `ComplexCharacterData` are in
`Langlands.LocalFactor.Archimedean`. `realStandardModule`, `realPositionCharacter`,
`realInducedFirstCharacter` and `realInducedSecondCharacter` are in `StandardModule.lean`.
`realBlockExponent`, `IsRealLanglandsOrdered` and `IsRealStandardIntertwiner` are in
`RealGenericParameterReduction.lean`.

## Real blocks and their standard modules (recalled from the Library)

A real block is one of two kinds:

- `.character c`, with `c : RealCharacterData`: the character `sgn^ε |·|^t` of `ℝ^×`, where
  `ε = c.parity` and `t = c.exponent ∈ ℂ`. It has rank one.
- `.induced d`, with `d : ComplexCharacterData`: the real induction of the character
  `(z/|z|)^m |z|^(2t)` of `ℂ^×`, where `m = d.weight ∈ ℤ` and `t = d.exponent ∈ ℂ`. It has
  rank two.

Its position characters are `sgn^(|m|+1) |·|^(t + |m|/2)` (`realInducedFirstCharacter`) and
`|·|^(t - |m|/2)` (`realInducedSecondCharacter`). In `realStandardModule N ds`, an induction
block cuts the principal series of its position characters down to the functions whose
Fourier coefficients of weight `|k| < |m|` along the rotations in its two coordinates vanish.
On `GL₂(ℝ)` this cut is the subrepresentation whose `SO(2)`-weights are `|k| ≥ |m| + 1`. For
`m ≠ 0` it is the discrete series `D_ℓ ⊗ |det|^t`, `ℓ = |m|`, in the notation of Knapp 1994
(`knapp-1994-archimedean-llc`, (2.1b) and (2.2b), printed pp. 399–400), whose lowest
`SO(2)`-weight is `ℓ + 1` (`StandardModule.md`, item 2). For `m = 0` it is the irreducible
principal series `Ind(sgn |·|^t ⊗ |·|^t)`, which is also the standard module of the two
characters `sgn |·|^t, |·|^t` (`StandardModule.md`, items 3 and 4).

In both cases `realBlockExponent` is `Re t`. A list `ds` is in Langlands order
(`IsRealLanglandsOrdered ds`) when these real parts are non-increasing along the list.

## Definitions

### `realBlockSupport : RealBlock → List ℂ`

- `.character c ↦ [c.exponent]`;
- `.induced d ↦ [d.exponent + |m|/2, d.exponent - |m|/2]` with `|m| = d.weight.natAbs` cast to
  `ℂ`.

These are the exponents `s` of the characters `|·|^s` (up to sign characters) at the block's
diagonal positions: the exponents of `realPositionCharacter` at those positions.

### `realExponentSupport (ds : List RealBlock) : List ℂ`

`ds.flatMap realBlockSupport`: the exponent supports of the blocks, concatenated in order.
Its length is `realRank ds` (`length_realExponentSupport`). Up to permutation it is the
infinitesimal character of the standard module, as an `S_N`-orbit in `ℂ^N`. The standard
module of `ds` is a submodule of the normalized principal series of these exponents, whose
infinitesimal character is that orbit. So two lists of blocks have permuted exponent supports
exactly when their standard modules have the same infinitesimal character.

### `realBlockWeightSquare : RealBlock → ℕ` and `realWeightSquareSum (ds : List RealBlock) : ℕ`

The squared weight of a block is `0` for a character block and `m^2 = (d.weight.natAbs)^2` for
an induction block. `realWeightSquareSum ds` is the sum over the blocks of `ds`.

Provenance of the four definitions: internal. They are bookkeeping functions read off the
Library's position characters. The connection with the Langlands parameter: let
`ν(ds) ∈ ℂ^N` be the vector repeating `t` at every position of a block with exponent `t`.
For the trace form,

`|Re ν(ds)|² = Σ_{s ∈ realExponentSupport ds} (Re s)² - realWeightSquareSum ds / 2`,

because an induction block contributes `(Re t + |m|/2)² + (Re t - |m|/2)² = 2 (Re t)² + m²/2` to
the first sum and `2 (Re t)²` to the left side. So, for a fixed exponent support, a smaller
`|Re ν|` is the same as a larger sum of squared weights.

## Statements

### `RealRankOneStepStatement.{uV}`

For every `n : ℕ`, every complex vector space `V : Type uV`, every `ρ` and `π`, every pair of
lists `pre post : List RealBlock` and blocks `x y : RealBlock`, and every
`B : kFiniteFunctions (realStandardModule n (pre ++ x :: y :: post)) (unitaryCompact ℝ n) →ₗ[ℂ] V`,
assume:

- `IsRealGKModule n ρ π`, `IsIrreducibleGKModule ρ π` and `IsAdmissibleGKModule ρ`;
- `realRank (pre ++ x :: y :: post) = n`;
- `realBlockExponent x < realBlockExponent y`;
- `B ≠ 0` and `IsRealStandardIntertwiner n ρ π (pre ++ x :: y :: post) B`.

Then one of the following holds:

1. (exchange) there is a nonzero `B'` on `realStandardModule n (pre ++ y :: x :: post)` with
   `IsRealStandardIntertwiner n ρ π (pre ++ y :: x :: post) B'`;
2. (replacement) there is `zs : List RealBlock` such that:
   - `(realExponentSupport zs).Perm (realExponentSupport [x, y])`;
   - `realWeightSquareSum [x, y] < realWeightSquareSum zs`;
   - there is a nonzero `B'` on `realStandardModule n (pre ++ zs ++ post)` with
     `IsRealStandardIntertwiner n ρ π (pre ++ zs ++ post) B'`.

The rank of `zs` is that of `[x, y]`, since the exponent supports have the same length.

Example on `GL₂(ℝ)` (`pre = post = []`). Take `x = |·|^{-1/2}` and `y = |·|^{1/2}`. The
discrete series `D_1`, with lowest `SO(2)`-weight 2, is the irreducible quotient of
`Ind(|·|^{-1/2} ⊗ |·|^{1/2})` by its trivial subrepresentation (as in
`RealGenericParameterReduction.md`). It is not a quotient of `Ind(|·|^{1/2} ⊗ |·|^{-1/2})`,
whose unique irreducible quotient is the trivial representation. So the exchange fails. The
replacement holds with `zs` the induction block of weight `1` and exponent `0`: its exponent
support is `[1/2, -1/2]`, its squared weight is `1 > 0`, and its standard module is `D_1`.

Provenance: derived. The statement is not in the literature in this form. It follows from the
Langlands classification for the factor `GL_r(ℝ)`, `r = rank x + rank y ≤ 4`, of a block Levi
subgroup, by the argument below. The argument is not in the cited texts. It combines the cited
results with standard facts, which are named where they are used and are not checked on a page
here.

Notation: `I(ds)` is the standard module of `GL_r(ℝ)` of a list `ds` of real blocks of total
rank `r`, in the Library's realization. `σ_pre` and `σ_post` are the standard modules of `pre`
and `post`. `Ind(σ_pre ⊗ W ⊗ σ_post)` is parabolic induction to `GL_n(ℝ)` from the block upper
triangular parabolic subgroup with Levi factor `GL_{r(pre)} × GL_r × GL_{r(post)}`.

1. **Induction in stages.** For `ws` equal to `[x, y]`, `[y, x]` or `zs`, the standard module
   of `pre ++ ws ++ post` is `Ind(σ_pre ⊗ I(ws) ⊗ σ_post)`. This is induction in stages
   (Knapp–Vogan 1995, `knapp-vogan-1995-cohomological-induction`, (11.196), printed p. 740,
   PDF p. 762; for the Library's realization, `StandardModule.md`, item 1). Parabolic induction
   is exact.
2. **The Langlands quotient of `I(y, x)`.** Replace each weight-zero induction block by its
   two characters; this does not change the standard module (`StandardModule.md`, item 4).
   - Then `I(y, x)` is induced from a cuspidal parabolic subgroup `MAN` of `GL_r(ℝ)`. Here `MA`
     is the block diagonal subgroup. `δ` is a sign character on each `GL_1` block and the
     discrete series `D_ℓ` of `SL^±_2(ℝ)` on each `GL_2` block (Knapp 1994, (2.1)–(2.2),
     printed pp. 399–400). `ν` is the exponent `t` of each block.
   - The positive `𝔞`-roots pair with `Re ν` as `Re t` of the earlier block minus `Re t` of
     the later block, in the Library's left-equivariant realization (see
     `IsRealLanglandsOrdered` in `RealGenericParameterReduction.md`). These differences are
     `≥ 0`: the two characters of a split weight-zero block have the same exponent, and
     `Re t(y) > Re t(x)`. So `I(y, x)` is a standard continuous-series representation in the
     sense of Knapp–Vogan, printed p. 739 (PDF p. 761).
   - Its associated standard tempered representation ((11.195), printed p. 740) is
     irreducible. `Re ν` vanishes only on the roots inside split weight-zero blocks. So that
     representation is the product of the sign characters, of the discrete series of the
     `GL_2` blocks, and of `Ind(sgn ⊗ 1)` on each split weight-zero block, up to unitary
     twists. Each factor is irreducible; for `Ind(sgn ⊗ 1)`, see `StandardModule.md`, item 3.
     This check of the definition is not in the cited texts.
   - By Knapp–Vogan Theorem 11.198(c), printed p. 741 (PDF p. 763), `I(y, x)` has a unique
     irreducible quotient `J(y, x)`.
3. **Composition factors.** `I(x, y)` and `I(y, x)` have the same composition factors, with
   multiplicities. They have the same character (`StandardModule.md`, item 4), and the
   characters of irreducible admissible representations are linearly independent
   (Harish-Chandra). Standard modules have finite length (Harish-Chandra).
4. **A composition factor that maps to `(ρ, π)`.** Let `0 = F₀ ⊂ ⋯ ⊂ F_k = I(x, y)` be a
   composition series. By exactness, the modules `Ind(σ_pre ⊗ F_j ⊗ σ_post)` filter the
   standard module of `pre ++ x :: y :: post`, with quotients
   `Ind(σ_pre ⊗ F_j/F_{j-1} ⊗ σ_post)`. Take the least `j` such that `B` is nonzero on the
   `j`-th step. Then `B` vanishes on the step before it. So `B` induces a nonzero intertwiner
   from `Ind(σ_pre ⊗ τ ⊗ σ_post)` to `(ρ, π)`, where `τ = F_j/F_{j-1}` is irreducible.
5. **Exchange.** Suppose `τ ≅ J(y, x)`. Compose with the surjection
   `Ind(σ_pre ⊗ I(y, x) ⊗ σ_post) → Ind(σ_pre ⊗ τ ⊗ σ_post)` given by exactness. This gives a
   nonzero intertwiner from the standard module of `pre ++ y :: x :: post`: alternative 1.
6. **Replacement.** Otherwise `τ` is, by step 3, a subquotient of `I(y, x)` not equivalent to
   `J(y, x)`.
   - By Knapp 1994, Theorem 1(a)–(b), printed p. 400 (PDF p. 410), `τ` is the unique
     irreducible quotient `J(zs)` of `I(zs)` for a list `zs` of real blocks in Langlands
     order. Here the order condition is corrected as in `RealGenericParameterReduction.md`.
     Knapp's blocks (2.2a) `1 ⊗ |·|^t` and `sgn ⊗ |·|^t` are the character blocks. His blocks
     (2.2b) `D_ℓ ⊗ |det|^t` are the induction blocks of weight `ℓ ≥ 1`.
   - As in step 2, `I(zs)` is a standard continuous-series representation with parameter
     `ν(zs)`. So `τ` has Langlands quotient parameters with `Re ν' = Re ν(zs)`, in the sense of
     Knapp–Vogan, Remark 2 after Theorem 11.198 (printed p. 741).
   - Knapp–Vogan, Remark 4 after Theorem 11.198 (printed p. 742, PDF p. 764), states two
     facts. First, `|Re ν|` is the same for all sets of Langlands quotient parameters of a
     given module. Second, if `V` has Langlands quotient parameters `(MAN, δ, ν)` and `V′` is
     another subquotient of `I(δ, ν)`, then the parameters of `V′` have `|Re ν′| < |Re ν|`.
     Take `V = J(y, x)` and `V′ = τ`. This gives `|Re ν(zs)| < |Re ν(y, x)|`.
   - The norm comes from an invariant form on `𝔤𝔩_r`, so it is `α Σ_i (Re ν_i)² + β (Σ_i Re ν_i)²`
     on diagonal vectors, with `α > 0`. Here `Σ_i ν_i` is the sum of the exponent support. So
     for permuted exponent supports, comparing `|Re ν|` is comparing it for the trace form.
   - `τ` has the infinitesimal character of `I(x, y)`, of which it is a subquotient, and of
     `I(zs)`, of which it is a quotient. By the Harish-Chandra isomorphism the exponent supports
     of `zs` and `[x, y]` are permutations of each other.
   - With the identity in the definitions section, for permuted exponent supports, the
     inequality reads `realWeightSquareSum zs > realWeightSquareSum [y, x]`, and
     `realWeightSquareSum [y, x] = realWeightSquareSum [x, y]`.
   - Compose with the surjection from `Ind(σ_pre ⊗ I(zs) ⊗ σ_post)`, the standard module of
     `pre ++ zs ++ post`. This gives alternative 2.

A proof must also identify the Library's algebraic `(𝔤, K)`-modules and `realStandardModule`
with the classical notions, as for the target (see `RealGenericParameterReduction.md`).

### `RealLanglandsFromRankOneStepReductionStatement.{uV}`

`RealRankOneStepStatement.{uV} → RealLanglandsFromPrincipalSeriesStatement.{uV}`.

Provenance: internal; the reduction is proved in this module.

## Lemmas

- `length_realBlockSupport d`: `(realBlockSupport d).length = d.rank`, by cases.
- `length_realExponentSupport ds`: `(realExponentSupport ds).length = realRank ds`. Proof by
  induction with `realRank_cons` and `length_realBlockSupport`.
- `realExponentSupport_append`, `realWeightSquareSum_append`: both functions turn `++` into
  `++` and `+`. Proof by `simp` (`List.flatMap_append`, `List.map_append`, `List.sum_append`).
- `realExponentSupport_swap pre post x y`: the exponent support of `pre ++ y :: x :: post` is a
  permutation of that of `pre ++ x :: y :: post`. Proof: `List.Perm.swap`, then
  `List.Perm.append_left` and `List.Perm.flatMap_right`.
- `realWeightSquareSum_swap pre post x y`: exchanging `x` and `y` keeps the sum of squared
  weights. Proof: the same permutation, then `List.Perm.map` and `List.Perm.sum_eq`.
- `realWeightSquareSum_le ds`: `(realWeightSquareSum ds : ℝ) ≤ 2 Σ_{s ∈ realExponentSupport ds}
  (Re s)²`. Proof by induction. A character block contributes `0` on the left and a square on
  the right. An induction block of weight `m` and exponent `t` contributes `m²` on the left and
  `2((Re t + |m|/2)² + (Re t - |m|/2)²) = 4 (Re t)² + m²` on the right. After `simp`
  (`Complex.add_re`, `Complex.sub_re`, `Complex.div_ofNat_re`, `Complex.natCast_re`),
  `nlinarith` closes the block case.
- `realInversionCount ds`: the number of pairs of blocks, the first before the second, with
  `realBlockExponent` strictly increasing. Recursively, `0` for `[]`, and for `a :: l` the
  number of `b ∈ l` with `realBlockExponent a < realBlockExponent b` (`List.countP`) plus the
  count of `l`.
- `realInversionCount_swap_lt pre post hxy`: if `realBlockExponent x < realBlockExponent y`, the
  count of `pre ++ y :: x :: post` is smaller than that of `pre ++ x :: y :: post`. Proof by
  induction on `pre`. For `pre = []`, the two counts differ by the term for the pair `x, y`.
  For `a :: pre`, the count of entries after `a` is unchanged, since `List.countP` is invariant
  under the permutation (`List.Perm.countP_eq`), and the induction hypothesis applies.
- `exists_adjacent_inversion_of_not_ordered`: a list that is not in Langlands order can be
  written `pre ++ x :: y :: post` with `realBlockExponent x < realBlockExponent y`. Proof by
  recursion on the list. For `a :: c :: l`:
  - If `c :: l` is in Langlands order and `Re t(a) ≥ Re t(c)`, then `a :: c :: l` is in
    Langlands order. The entries of `l` have `Re t ≤ Re t(c) ≤ Re t(a)`. This contradicts the
    hypothesis.
  - If `Re t(a) < Re t(c)`, take `pre = []`.
  - Otherwise the recursive call on `c :: l` gives the decomposition, and `a` is prepended to
    `pre`.

## The reduction: `realLanglandsFromPrincipalSeries_of_rankOneStep`

It proves `RealLanglandsFromRankOneStepReductionStatement.{uV}`. Fix the data of the target:
`cs` with `cs.length = n` and a nonzero intertwiner `B` from the standard module of
`cs.map RealBlock.character`. Let `S₀` be the exponent support of that list, of length `n`.
Let `K = ⌊2 Σ_{s ∈ S₀} (Re s)²⌋₊`.

- Every list `ds` whose exponent support is a permutation of `S₀` has `realRank ds = n`
  (`length_realExponentSupport`, `List.Perm.length_eq`). It also has
  `realWeightSquareSum ds ≤ K`: by `realWeightSquareSum_le`, by `List.Perm.sum_eq` for the
  squared real parts, and by `Nat.le_floor`.
- The claim proved is: for all `a b : ℕ` and every list `ds` with
  `K - realWeightSquareSum ds = a`, `realInversionCount ds = b`, exponent support a
  permutation of `S₀` and a nonzero intertwiner from its standard module, the conclusion of
  the target holds. The proof is by strong induction on `a` (`Nat.strong_induction_on`) and,
  inside, by strong induction on `b`. The target follows by applying the claim to
  `cs.map RealBlock.character`, with `List.Perm.refl`.
- In the induction step:
  - If `ds` is in Langlands order, it is the required list, since its rank is `n`.
  - Otherwise `exists_adjacent_inversion_of_not_ordered` writes `ds = pre ++ x :: y :: post`
    with `Re t(x) < Re t(y)`, and `RealRankOneStepStatement` applies.
  - Exchange: the new list `pre ++ y :: x :: post` has a permuted exponent support
    (`realExponentSupport_swap`) and the same sum of squared weights
    (`realWeightSquareSum_swap`), so the same `a`. It has fewer inversions
    (`realInversionCount_swap_lt`). The inner induction hypothesis applies.
  - Replacement: the new list `pre ++ zs ++ post` has exponent support
    `S(pre) ++ S(zs) ++ S(post)`, a permutation of `S(pre) ++ S([x, y]) ++ S(post)`, which is
    the support of `ds` (`realExponentSupport_append`, `List.Perm.append_left`,
    `List.Perm.append_right`). Its sum of squared weights is strictly larger
    (`realWeightSquareSum_append` and the strict inequality for `zs`) and still at most `K`.
    So its `a` is smaller (`omega`), and the outer induction hypothesis applies.

The proof uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
