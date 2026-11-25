# The filtration of real standard modules for two adjacent characters

Module: `Langlands.Representation.Archimedean.RealCharacterPairFiltration`. The generic case
`realAdjacentFiltration_of_generic` is in namespace
`Langlands.Archimedean.RealCharacterPairReducible`; the main theorem
`realCharacterPairFiltration` is in namespace `Langlands.Archimedean`.

## Statement proved

`realCharacterPairFiltration : RealCharacterPairFiltrationStatement`, the statement defined
in module `RealRankOneStepFiltration`. Let `c`, `d` be characters of `ℝ^×` with
exponents `t_c`, `t_d` and `Re t_c < Re t_d`, and let `pre`, `post` be lists of real blocks
with `realRank (pre ++ character c :: character d :: post) = n`. Then
`RealAdjacentFiltration n pre post (character c) (character d)` holds. That is, there are
finitely many lists `ws j` and linear maps `q j` from the `O(n)`-finite functions of the
standard module of `pre ++ ws j ++ post` to those of `pre ++ character c :: character d :: post`
with three properties. Each `ws j` is `[d, c]`, or has the same exponent support as `[c, d]`
and a larger sum of squared weights. Each `q j` is an intertwiner modulo the span of the
earlier ranges. The ranges span.

## Notation

As in module `RealCharacterPairReducible`: `src = pre ++ character c :: character d :: post`,
`swp = pre ++ [character d, character c] ++ post`,
`K(ds) = kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`, `p = realRank pre`,
`ε = pairParity c d ∈ {0, 1}` (module `RealCharacterPairData`), `ν = t_d - t_c`, and
`sigma0 c d = (-1)^{ε.natAbs}`.

## The generic case

**`realAdjacentFiltration_of_generic hn hlt hne`**: for `hn : realRank src = n`,
`hlt : Re t_c < Re t_d` (stated with `realBlockExponent`) and
`hne : ∀ m : ℕ, ν ≠ ε + 2m + 1`, `RealAdjacentFiltration n pre post (character c) (character d)`
holds with one piece: `k = 1`, `ws 0 = [character d, character c]` and `q 0 = q₀`.

Proof.

1. `0 < Re ν` by `exponent_sub_re_pos hlt`. Let `μ = genericMultiplier ν ε` (module
   `RealBlockMultiplier`). It is symmetric with sign `(-1)^{ε.natAbs} = sigma0 c d`
   (`isSymmetric_genericMultiplier`). It is recurrent for `δ = ν + 1`
   (`isRecurrent_genericMultiplier`, using `0 < Re ν`). It has no zeros
   (`genericMultiplier_ne_zero`, using `0 < Re ν` and `hne`).
2. `q₀ = blockFrobMap (data_swap hn hsym) : K(swp) → K(src)` and
   `B = blockFrobMap (data_unswap hn hsym) : K(src) → K(swp)`, with multipliers `μ` and the
   pointwise inverse `μ⁻¹`.
3. On `swp` the exponents at `p`, `p + 1` are `t_d`, `t_c` (`exponent_swp_zero`,
   `exponent_swp_one`). So the ρ-shifted difference that `isRealIntertwinerModulo_blockFrobMap`
   asks about is `t_d - t_c + 1 = ν + 1`. The recurrence of step 1 makes `q₀` an
   intertwiner modulo every subspace, in particular modulo the empty span `⨆_{i < 0}`.
4. `q₀ (B g) = g` for every `g ∈ K(src)` by `blockFrobMap_blockFrobMap_eq`. Its hypothesis
   concerns the `j` with `μ_j μ_j⁻¹ ≠ 1`, and there are none, since `μ_j ≠ 0`. Hence
   `range q₀ = ⊤`, which is the spanning condition.

## The main theorem

By `generic_or_reducible`, either `ν ≠ ε + 2m + 1` for every `m : ℕ` (the generic case
above), or `ν = ℓ` with `ℓ > 0` and `ℓ - 1 ≡ ε (mod 2)` (the reducible case,
`RealCharacterPairReducible.realAdjacentFiltration_of_reducible`, with the two pieces `[d, c]`
and `[induced (pairInduced c d ℓ)]`). `RealCharacterPairReducible.realCharacterPairFiltration_of_generic`
performs this case split, so `realCharacterPairFiltration` applies it to
`realAdjacentFiltration_of_generic`.

All maps are Frobenius maps along the block of the pair (module `RealBlockFrobeniusMap`). They
use the block Jacquet functionals of module `RealBlockJacquetFunctional` and the multipliers of
module `RealBlockMultiplier`; see the Markdown of those modules.

Axioms of `realCharacterPairFiltration`: `propext`, `Classical.choice`, `Quot.sound`.
