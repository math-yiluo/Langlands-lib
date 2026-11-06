# A block with irreducible Weil factor is indecomposable

Worker 1429 supplies helper definitions and proved lemmas about the published
uncentered blocks `block ν A m = A ⊗ S_m` of `Langlands.WeilDeligne.SpecialBlocks`
and the published direct sum `directSum` of `Langlands.WeilDeligne.DirectSum`.
The main result is `Blocks.isIndecomposable_block`: for an irreducible finite
complex representation `σ` of an arbitrary group `G`, an arbitrary character
`ν : G →* ℂˣ` and any `m : ℕ`, the block `σ ⊗ S_(m+1)` is indecomposable in the
published sense `IsIndecomposable` of `Langlands.WeilDeligne.BlockStatements`.
Nothing here assumes a classification of indecomposable pairs.

## Declarations

All names are in `Langlands.WeilDeligneRepresentation`.

| Declaration | Content |
| --- | --- |
| `Special.lowering K m` | The linear map on `Fin (m+1) → K` that moves coordinate `j+1` to `j` for `j < m` and puts `0` at the top coordinate `m`. |
| `Special.lowering_apply` | Its value at each coordinate. |
| `Special.lowering_raising_add` | `lowering (raising w) + w_top • e_top = w`: lowering undoes the published raising map away from the top coordinate. |
| `Special.topEmbedding V m` | The linear map `a ↦ a ⊗ e_top` from `V` to `V ⊗ (Fin (m+1) → K)`, where `e_top = Special.topVector K m`. |
| `Special.topProjection V m` | The linear map `a ⊗ w ↦ w_top • a`. |
| `Special.topEmbedding_apply`, `Special.topProjection_tmul`, `Special.topProjection_topEmbedding` | Their values on pure tensors; the projection is a left inverse of the embedding. |
| `Special.lTensor_lowering_raising_add` | Every tensor `x` equals `(1 ⊗ lowering)((1 ⊗ raising) x)` plus the image of `x` under projection followed by embedding. |
| `Special.topEmbedding_topProjection_of_lTensor_raising` | A tensor killed by `1 ⊗ raising` lies on the top-weight line: it is the embedding of its own projection. |
| `block_monodromy_apply` | The monodromy of `block ν A m` is `1 ⊗ raising` (the Weil factor carries zero monodromy). |
| `block_representation_topEmbedding` | On the top-weight line, `g` acts by `ν(g)^m` times the action of `g` on `A`: `g · (a ⊗ e_top) = ν(g)^m (g a ⊗ e_top)`. |
| `directSumFinOneLinearEquiv X` | For a family `X : Fin 1 → WeilDeligneRepresentation K G ν`, the linear isomorphism from `⨁_{i : Fin 1} X i` to `X 0` given by the zeroth component. |
| `component_directSum_monodromy` | The zeroth component commutes with the componentwise monodromy. |
| `directSumFinOneEquiv X` | The published pair equivalence `Equiv (directSum X) (X 0)`: the linear isomorphism above intertwines both the Weil actions and the monodromies. |
| `Blocks.IsIndecomposable.of_equiv` | If complex pairs `A` and `B` (possibly in different carrier universes) are equivalent and `A` is indecomposable, then `B` is indecomposable. |
| `Blocks.exists_ne_zero_of_isIrreducible` | An irreducible representation has a nonzero vector (its zero subrepresentation differs from the top one). |
| `Blocks.isIndecomposable_block` | For an irreducible `A` and `m : ℕ`, `block ν A (m+1)` is indecomposable. |

The field `K`, the group, and the carrier universes are arbitrary in the
algebraic lemmas; the indecomposability lemmas use complex coefficients
because the published `IsIndecomposable` is stated over `ℂ`.

## Proofs

**Lowering and the top-weight line.** The published raising map on
`Fin (m+1) → K` sends coordinate `j` to `j+1` and drops the top coordinate. A
coordinatewise computation shows `lowering (raising w) = w - w_top • e_top`.
Tensoring with `V` and inducting over tensors gives
`x = (1 ⊗ lowering)((1 ⊗ raising) x) + topEmbedding (topProjection x)`.
When `(1 ⊗ raising) x = 0` the first summand vanishes, so `x` is on the
top-weight line.

**Block action and monodromy.** The block monodromy is by definition
`0 ⊗ 1 + 1 ⊗ raising`, so it equals `1 ⊗ raising`. The Weil action on the
special factor sends `e_top` to `ν(g)^m e_top` (the published
`Special.action_topVector`), which gives the action on `a ⊗ e_top`.

**One-term direct sum.** The zeroth component and the zeroth inclusion are
inverse because `Fin 1` has one element; both actions and the monodromy act
componentwise, so the zeroth component intertwines them by definition.

**Transport of indecomposability.** Let `f : A ≃ B` be the linear
isomorphism of an equivalence. Preimages under `f` of stable subspaces are
stable, because `f` commutes with the actions and the monodromies, and taking
preimages along a linear isomorphism is an order isomorphism of subspace
lattices, so complementary pairs go to complementary pairs and `⊥` corresponds
to `⊥`. Nontriviality transfers along `f⁻¹`.

**Indecomposability of the block.** Write `X = block ν A (m+1)`,
`ι = topEmbedding` and `φ = topProjection`. For a stable subspace `S` of `X`,
the preimage `ι⁻¹(S)` is a subrepresentation of `A`: if `ι a ∈ S` then
`g · ι a = ν(g)^m ι(g a) ∈ S`, and `ν(g)^m` is invertible. If this preimage is
zero, then `S = 0`: a vector `y ∈ S` with `N y = 0` satisfies `y = ι(φ y)`, so
`φ y ∈ ι⁻¹(S) = 0` and `y = 0`. By induction on `k`, every `y ∈ S` with
`N^k y = 0` is zero (apply the previous case to `N^{k-1}`-images, which stay in
`S` by stability), and the published nilpotence of the block monodromy gives
`S = 0`. Now let `S, T` be complementary stable subspaces. Irreducibility of
`A` makes each of `ι⁻¹(S)`, `ι⁻¹(T)` either zero or all of `A`. If either is
zero, the corresponding subspace is zero. Otherwise a fixed nonzero `a₀ ∈ A`
satisfies `ι a₀ ∈ S ∩ T = 0`, contradicting `φ(ι a₀) = a₀ ≠ 0`. The same
nonzero vector `ι a₀` shows that `X` is nontrivial.

## Provenance

This is internal infrastructure, not a numbered theorem of a source. It
records the elementary half of Henniart 2002, §2.3 (printed p.594), where
`(ρ, n) ↦ ρ ⊗ St_n` maps irreducible `ρ` and `n ≥ 1` into the indecomposable
classes `G_2`: a single block `σ ⊗ S_(m+1)` with `σ` irreducible is an
indecomposable Weil–Deligne pair, here in the uncentered block convention of
the published `SpecialBlocks` module. It is needed to show that an essentially
square-integrable assembly image comes from an indecomposable parameter.
