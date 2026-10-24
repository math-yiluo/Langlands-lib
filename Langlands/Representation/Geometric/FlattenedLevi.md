# Actual flattened coordinates for a refined Levi

Author: Worker 125.

This module constructs `Langlands.Geometric.flattenedLeviEquiv R B S`, a
multiplicative equivalence

```lean
(B.flatten S).Levi R ≃* Geometric.refinedLevi R B S
```

for every commutative ring `R`, block shape `B : BlockShape n`, and refinement
`S : BlockRefinement B`. The codomain is the existing subgroup of `B.Levi R`.
The forward map groups the fine matrices into their actual outer blocks and
embeds each group by the published inner block-diagonal embedding. There is
no supplied group equivalence or decomposition hypothesis. Every inverse,
multiplicativity, embedding, and continuity obligation is proved.

This is a derived internal coordinate construction for standard type-A nested
Levi geometry. Its inputs are the published `flatten`, `flattenBlockEquiv`,
`flatten_size_flattenBlockEquiv`, and `flatten_index` in
`CuspidalSupport.MinimalJacquetProof`, the actual subgroup identification
`refinedLeviEquiv` in `Geometric.RefinementDefinitions`, and the matrix and
topological maps in `Group.GL.Basic` and `Group.GL.Blocks`. It does not claim
that an original literature source states these Lean coordinate maps; no
external source is cited for this internal construction. The imported files
are unchanged.

## Reindexing and component formulas

Write `C = B.flatten S`, `e = B.flattenBlockEquiv S`, and
`hᵢⱼ = B.flatten_size_flattenBlockEquiv S ⟨i,j⟩`. Thus
`hᵢⱼ : C.size (e ⟨i,j⟩) = (S i).size j`. The intermediate equivalence
`flattenedLeviProductEquiv R B S` identifies `C.Levi R` with
`∀ i, (S i).Levi R`. Its inverse sends a nested tuple `t` to

```text
k ↦ t (e.symm k).1 (e.symm k).2.
```

Here the block sizes are definitionally equal, so this formula needs no
transport. It is `flattenedLeviProductEquiv_symm_apply`. The construction
uses dependent currying and `Equiv.piCongrLeft'`; pointwise multiplication
makes the inverse reindexing multiplicative. Their proved inverse laws
supply the inverse equivalence. The lemma
`flattenedLeviProductEquiv_apply_symm` says that the nested coordinate
indexed by `e.symm k` of the forward image is exactly `m k`.

For named outer and inner indices, `flattenedLeviProductEquiv_apply` states

```text
(flattenedLeviProductEquiv R B S m) i j
  = GeneralLinear.reindex (finCongr hᵢⱼ) (m (e ⟨i,j⟩)).
```

This simultaneously relabels the rows and columns along the actual size
equality. In entries, its value at `a,b : Fin ((S i).size j)` is the entry
of `m (e ⟨i,j⟩)` at `Fin.cast hᵢⱼ.symm a, Fin.cast hᵢⱼ.symm b`.
The proof reduces the dependent equality `e.symm k = ⟨i,j⟩` to reflexivity
and applies the coordinate identity above.

The main equivalence composes this reindexing with the published
`refinedLeviEquiv R B S`. Its formulas are:

- `flattenedLeviEquiv_component`: applying `refinedLeviEquiv.symm` to its
  forward image gives precisely the size-transported matrix above.
- `flattenedLeviEquiv_symm_component`: for a refined element `r`, its inverse
  image at `e ⟨i,j⟩` is
  `(GeneralLinear.reindex (finCongr hᵢⱼ)).symm
  ((refinedLeviEquiv R B S).symm r i j)`.
  This follows by injectivity of the reindexing map and the forward formula.

Thus both directions identify the actual fine matrix, including its index
type, rather than merely asserting an abstract group isomorphism.

## Ambient embedding and topology

`flattenedLeviEquiv_embedding` proves

```lean
B.leviEmbedding R (flattenedLeviEquiv R B S m).val =
  (B.flatten S).leviEmbedding R m
```

as an equality in `GeneralLinear n R`. The proof tests every matrix entry
using the flattened index equivalence. On the same fine block, `flatten_index`
turns its coordinates into nested coordinates; two applications of
`leviEmbedding_apply_same` and the product coordinate formula give the
original entry. On different fine blocks, either their outer blocks differ,
or the outer blocks agree and their inner blocks differ. The corresponding
published `leviEmbedding_apply_ne` gives zero in each case. Injectivity of
`e.symm` rules out equality of both indices. The inverse embedding identity
is `flattenedLeviEquiv_symm_embedding`, obtained by the inverse law.

For `[TopologicalSpace R] [IsTopologicalRing R]`,
`flattenedLeviProductEquivContinuous` packages the same product reindexing
as a continuous multiplicative equivalence. Forward continuity follows
coordinatewise from `reindexContinuous` and continuous evaluation; inverse
continuity is two successive coordinate evaluations.
`flattenedLeviEquivContinuous` composes this with the published
`refinedLeviEquivContinuous`. Its underlying multiplicative equivalence is
definitionally `flattenedLeviEquiv`.

No hypothesis `0 < n` is introduced. All present block sizes are positive
by `BlockShape`; the empty rank-zero shape and its empty products are
included. Nothing assumes a nontrivial coefficient ring.

## Representation and character consumers

For a field `F` and an actual representation
`ρ : Representation ℂ (refinedLevi F B S) V`, pull back by

```lean
ρ.comp (flattenedLeviEquiv F B S).toMonoidHom
```

This is a representation of `(B.flatten S).Levi F` on the same `V`.
With the appropriate field topology, the existing predicate
`CuspidalSupport.IsLeviCuspidal (B.flatten S)` applies directly to it.
That predicate retains both admissibility and quasicuspidality. This module
does not assert that a given representation satisfies it. For a topological
field, `isSmooth_comp` uses the continuity of
`flattenedLeviEquivContinuous` to pull back smoothness. These expressions
impose no equality between the field and representation carrier universes;
no additional representation helper or carrier restriction is introduced.

For a p-adic field with compatible topological data `T`, fine-block
characters are the existing `T.blockDeterminantNorm (B.flatten S) k`.
After importing `Langlands.Representation.Twist.LeviRealPower`, the existing
`T.leviRealPowerCharacter (B.flatten S) t` and
`T.leviRealPowerTwist (B.flatten S) t` give fine-block real determinant
characters and twists of the pulled-back representation. A character `χ`
on the flattened product becomes a character on the refined subgroup by
`χ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom`.
The component formulas specify the fine block to which each exponent
belongs. These are instructions for using existing APIs, not new cuspidality,
Jacquet equivalence, transitivity, Haar-modulus, or classification theorems.
