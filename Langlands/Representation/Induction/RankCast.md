# Normalized product induction along an equality of total ranks

Author: Worker 837.

This internal adapter module transports the actual normalized product induction
`i(σ_1, …, σ_r)` of `Induction/BlockFactors` along an equality of total ranks
`h : m = n`. Let `B` be a block shape of total rank `m`. The cast shape
`B.rankCast h` of `Group/GL/SingleBlock` has total rank `n` and the same length
and block sizes, so the same factor family `σ` serves for both shapes.

All data is explicit precomposition by the entry-preserving reindex
`GL_m(F) ≃* GL_n(F)` along `finCongr h`, or by its inverse. The equality `h` is
eliminated (`subst h`) only inside proofs of propositions: subgroup membership,
the agreement of Levi projections and modulus characters, and the agreement of
the inducing representations. No function or representation is transported by
a cast. The module introduces no new hypotheses on the representations, and it
modifies no existing Library module.

## Generic transport along a group isomorphism

Here `G` and `H` are topological groups, `P ≤ G` and `Q ≤ H` are subgroups, and
`σ` and `τ` are representations of `P` and `Q` on the same module `V` over a
commutative ring `R`. These declarations are in the namespace
`Langlands.Induction`.

- `comapSmoothFunction φ hφ hPQ hστ f` takes a continuous homomorphism
  `φ : G →* H` that carries `P` into `Q`, with `τ(φ p) = σ(p)` for `p ∈ P`. It
  sends a smooth `Q`-covariant function `f` on `H` to the function
  `x ↦ f(φ x)` on `G`. The result is `P`-covariant: `f(φ(p x)) = τ(φ p) f(φ x)
  = σ(p) f(φ x)`. It is smooth: if `f` is invariant under right translation by
  an open subgroup `K` of `H`, then `x ↦ f(φ x)` is invariant under the open
  subgroup `φ⁻¹(K)`. The value formula `comapSmoothFunction_eval` holds by
  definition.
- `comapSmoothInducedEquiv φ hφ hφ' hPQ hστ` takes a group isomorphism
  `φ : G ≃* H` such that `φ` and `φ⁻¹` are continuous, and `φ g ∈ Q` if and
  only if `g ∈ P`. It also requires `τ(φ p) = σ(p)` for `p ∈ P`. It is a
  `Representation.Equiv` from smooth induction `smoothInduced Q τ`, pulled back
  along `φ`, to `smoothInduced P σ`. The forward map is
  `comapSmoothFunction φ`. The inverse map is `comapSmoothFunction φ⁻¹`; two
  private lemmas show that `φ⁻¹` carries `Q` into `P` and matches `τ` with `σ`.
  The two maps are mutually inverse because `φ (φ⁻¹ y) = y` and
  `φ⁻¹ (φ x) = x`. They intertwine because `φ` is multiplicative:
  `f(φ x · φ g) = f(φ(x g))`.
- `comapSmoothInducedEquiv_eval` and `comapSmoothInducedEquiv_symm_eval` give the
  values: the forward image of `f` takes the value `f(φ x)` at `x`, and the
  inverse image takes the value `f(φ⁻¹ y)` at `y`. Both hold by definition.

## Reindexing general linear groups along an equality of ranks

These facts concern the published `GeneralLinear.reindex (finCongr h)`, the
entry-preserving isomorphism `GL_m(R) ≃* GL_n(R)` for `h : m = n`.
They are imported from the shared
[`Group/GL/RankReindex`](../../Group/GL/RankReindex.md) pair.

- `reindex_finCongr_apply` and `reindex_finCongr_symm_apply`: the forward and
  inverse reindex read matrix entries at the indices cast along `h⁻¹` and `h`.
- `reindex_finCongr_rfl`: along `rfl`, the reindex is the identity isomorphism.
- `continuous_reindex_finCongr` and `continuous_reindex_finCongr_symm`: for a
  commutative ring `R` with any topology, the reindex and its inverse are continuous. They are
  the two directions of the published homeomorphism `reindexContinuous`.

## Parabolic data of the cast shape

These declarations are in the namespace `Langlands.GeneralLinear.BlockShape`.

- `rankCast_rfl`: the shape cast along `rfl` is `B` itself.
- `reindex_mem_rankCast_parabolic_iff`: the reindex of `g ∈ GL_m(R)` lies in
  the standard parabolic of `B.rankCast h` if and only if `g` lies in the
  standard parabolic of `B`.
- `rankCast_leviProjection_reindex`: for `p` in the standard parabolic of `B`,
  the Levi projection of `B.rankCast h` at the reindexed element is the Levi
  projection of `B` at `p`. The Levi groups of the two shapes coincide, since
  they have the same block sizes.

## The transport of normalized product induction

These declarations are in the namespace `Langlands.PadicField.TopologicalData`.
Here `T` is a topological datum on the `p`-adic field `F`. The factor family
`σ_i : GL_{n_i}(F) → GL(V_i)` is indexed by the blocks of `B`. The carriers
`V_i` lie in a universe `uV` that is independent of the universe of `F`.

- `parabolicHalfModulus_rankCast_reindex`: the positive half modulus of
  `B.rankCast h` at the reindexed parabolic element equals the positive half
  modulus of `B` at the original element.
- `rankCast_inducing_reindex`: the inducing representations agree along the
  reindex. On the cast side, the inducing representation is the twist by the
  half modulus of `B.rankCast h` of the block tensor `B.blockTensor σ` composed
  with the Levi projection of `B.rankCast h`. This is definitionally the
  inducing representation of `T.normalizedProductInduced (B.rankCast h) σ`,
  because the cast shape has the same blocks.
- `T.normalizedProductInducedRankCastEquiv B h σ` is a `Representation.Equiv`
  from `(T.normalizedProductInduced (B.rankCast h) σ).comp
  (GeneralLinear.reindex (R := F.Carrier) (finCongr h)).toMonoidHom` to
  `T.normalizedProductInduced B σ`. The source is the normalized product over
  the cast shape, a representation of `GL_n(F)`, pulled back to `GL_m(F)` along
  the reindex. The type names the factor carriers' module instances explicitly
  as those of `B`. The definition is `comapSmoothInducedEquiv` applied to the
  reindex, using the continuity, parabolic membership and inducing
  representation facts above.
- `normalizedProductInducedRankCastEquiv_eval`: the forward image of a function
  `f` on `GL_n(F)` takes the value `f(reindex x)` at `x ∈ GL_m(F)`.
- `normalizedProductInducedRankCastEquiv_symm_eval`: the inverse image of a
  function `f` on `GL_m(F)` takes the value `f(reindex⁻¹ y)` at `y ∈ GL_n(F)`.

Both value formulas hold by definition and are `simp` lemmas. In them, the
function spaces are written with the definitionally equal inducing
representations of `rankCast_inducing_reindex`.

## Provenance

The provenance is internal: equality transport along `h : m = n`, carried out
as precomposition with the entry-preserving reindex and its inverse. No
literature result is formalized here. The generic layer is the standard fact
that a topological group isomorphism matching the inducing data identifies the
smooth induced representations by precomposition. This module proves no
regrouping or associativity statement for normalized product induction.
