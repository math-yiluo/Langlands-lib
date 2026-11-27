# Jacquet nonvanishing in standard level-zero coordinates

The theorem `not_subsingleton_coinvariants_coarseN` takes the standard unit
group `U(𝔄)` in `GL (Fin f × Fin e) F` with `e > 0` and the compact open
subgroup `K = U^1(𝔄)`. A finite-dimensional representation `ρ` of `U(𝔄)` is
trivial on `K`, and its sums `∑_Z ρ(diag(unipLift r Z, 1))` on blocks `0, m`
vanish for `m > 0` and `0 < r < f`. If there is a nonzero intertwining map
from `ρ` to the restriction of a smooth representation `π`, then
`Jacquet.Coinvariants π (coarseN F f he)` is nonzero. This is the matrix
version used to prove the level-zero consequence of BK93 (7.3.2).
[Source details](LevelZeroNonmaximalTypeJacquetProof.md#source)

Use `not_subsingleton_coinvariants_of_compression` with `aElt` and the weak
contraction, factorization and exhaustion lemmas of `LevelZeroCoarse`. Every
intertwining map takes values in the `K`-fixed vectors. Compression by `aElt`
preserves intertwining. To see this, factor `x ∈ U(𝔄)` as `l m u` by
`coarse_factor`. The type acts by `ρ(m)` because `l, u ∈ K`. The element `m`
commutes with `aElt` and normalizes `K`, so its action commutes with
compression. The factors `l` and `u` fix the compressed vectors and their
`m`-translates. The lemma `compressionMap_aElt_comp_eq_zero` gives the
injectivity hypothesis, and the criterion applies to the given nonzero map.
