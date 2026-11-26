# The transformation law of the Levi Whittaker coefficient at one unramified place

Module `Langlands.Global.Factors.CuspidalPairEisensteinOneplaceLaw`, namespace
`Langlands.Global.CuspidalPairEisenstein.Oneplace`.

The module proves that the Levi Whittaker coefficient `W_M(φ_s)` of a twisted section
(see [CuspidalPairEisensteinOneplace.md](CuspidalPairEisensteinOneplace.md)) transforms, under
right translation by a matrix supported at an unramified finite place `v`, by the normalized
spherical section `f_v` of the local two-block induced representation
(`Shahidi.UnramifiedSection.sectionFunction`, see
[UnramifiedOpenCellSection.md](../../Representation/Shahidi/UnramifiedOpenCellSection.md)).

## Content

### Naturality and rank transport

For a ring homomorphism `f : R →+* S`, the induced map `Matrix.GeneralLinearGroup.map f`
commutes with reindexing (`map_reindex`), with the block unipotent matrices
(`map_sumBlockUnipotent`, `map_upper`, `map_intertwiningUnipotent`), with permutation matrices
(`map_permutation`, `map_blockWeyl`) and with block-diagonal embeddings (`map_leviEmbedding`).
For a block shape `C` and `h : m = n`, the Levi embedding of `C.rankCast h` is the reindexed
Levi embedding of `C` (`leviEmbedding_rankCast`), and reindexing maps the unipotent radical of
`C` into that of `C.rankCast h` (`reindex_mem_unipotentSubgroup_rankCast`).

### Matrices supported at one place

- `adelicAt F n v x`: the adelic matrix with component `x ∈ GL_n(F_v)` at `v` and `1` at every
  other place, finite or archimedean; `adelicAt_mul`.
- `comp_eq_map`, `infinite_eq_map`: the component maps as `Matrix.GeneralLinearGroup.map` of
  the projections; `comp_adelicAt`, `comp_adelicAt_of_ne`, `infinite_adelicAt`.
- `adelic_ext`: an adelic matrix is determined by its archimedean component and its finite
  components.
- `commute_adelicAt`: an adelic matrix with component `1` at `v` commutes with every
  `adelicAt v x`.
- `adelicAt_mem_standardCompact`: `adelicAt v x` lies in the standard maximal compact
  subgroup when `x ∈ GL_n(𝒪_v)`.
- `adelicAt_apply_eq_zero`, `adelicAt_apply_eq_one`, `adelicAt_mem_unipotentSubgroup`: an
  element of the unipotent radical of a block parabolic of `GL_n(F_v)`, placed at `v`, lies in
  the adelic unipotent radical.
- `adelicAt_leviEmbedding`: a block-diagonal matrix placed at `v` is the adelic Levi element
  with blocks placed at `v`.

### The two-block case

- `blockEquiv r t : Fin ((r+1)+(t+1)) ≃ Fin (r+t+2)` and `blockAt F r t v x`, the matrix
  `x ∈ GL_((r+1)+(t+1))(F_v)` reindexed to size `r+t+2` and placed at `v`; `blockAt_mul`.
- `blockAt_mem_unipotentSubgroup`: the unipotent radical of the local upper two-block
  parabolic is mapped into the adelic unipotent radical of `blockShape r t`.
- `blockAt_blockSum`: `blockAt v (diag(m₁, m₂))` is the Levi element `localLevi F r t v m₁ m₂`
  of [CuspidalPairEisensteinOneplace.md](CuspidalPairEisensteinOneplace.md).
- `reindex_mem_localIntegral`: a matrix integral for the canonical valuation of
  `CompletionPadic.padicField v` is integral at `v` after reindexing.
- **`leviWhittaker_mul_blockAt`**: let `φ` be a section built from cusp forms spherical outside
  `S`, `v ∉ S` a finite place where the canonical component `ψ_v` of `ψ` has additive
  conductor `0`, `a` and `c` Satake tuples of `P` and `Pd` at `v`, and `g` an adelic matrix with
  component `1` at `v`. Then for every `x ∈ GL_((r+1)+(t+1))(F_v)`,
  `W_M(φ_s)(g · blockAt v x) = f_v(x) · W_M(φ_s)(g)`.

## Proof of `leviWhittaker_mul_blockAt`

Write `x = p k` with `p` in the local upper two-block parabolic and `k` integral
(`Shahidi.UnramifiedSection.exists_parabolic_mul`), and `p = u · diag(m₁, m₂)` with `u` in the
unipotent radical (`BlockShape.unipotentPart`). Then `f_v(x) = leviValue(m₁, m₂)`
(`sectionFunction_parabolic_mul`), and
`g · blockAt v x = g · U · M · K` with `U = blockAt v u`, `M = blockAt v (diag(m₁, m₂))` and
`K = blockAt v k`.

1. `φ_s` is right invariant under `K`: `φ` by the sphericity clause of
   `IsSphericalSectionOutside` at `v`, and `H^s` because `K` lies in the standard maximal
   compact subgroup. Hence `W_M(φ_s)(g U M K) = W_M(φ_s)(g U M)`.
2. `g` has component `1` at `v`, so it commutes with `U` and `M`: `g U M = U (M g)`.
3. `U` lies in the adelic unipotent radical, so `W_M(φ_s)(U (M g)) = W_M(φ_s)(M g)`
   (`leviWhittaker_unipotent_mul`, `twisted_unipotent_mul`).
4. `M = localLevi v m₁ m₂` (`blockAt_blockSum`), and `leviWhittaker_localLevi_mul` gives
   `W_M(φ_s)(M g) = leviValue(m₁, m₂) W_M(φ_s)(g)`; the integral triviality of the standard
   characters of `ψ_v` comes from the conductor hypothesis
   (`UnequalEulerFactorization.isIntegrallyTrivial_standardCharacters`).

## Provenance

This is the statement, in the proof of Shahidi (1981), Theorem 5.1, pp. 351–352
(`shahidi-1981-certain-l`), that at a place `v` outside the ramification the local component
at `v` of the Whittaker coefficient of a section induced from cusp forms is the normalized
spherical section of the local induced representation, whose Jacquet integral is computed by
Casselman–Shalika (1980), Theorem 5.4 (`casselman-shalika-1980-whittaker`). The proof above is
internal.
