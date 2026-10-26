# Actual allowed-entry coordinates for the full correction subgroup

Author: Worker 201.

This internal construction gives actual matrix-entry coordinates for the full
subgroup `U ∩ g⁻¹ Q g`, where `U = B.unipotentSubgroup R`,
`Q = C.parabolic R`, and `g = GeneralLinear.permutation n R w`.
All declarations are in `Langlands.Geometric`. The ring `R : Type u` is an
arbitrary commutative ring in an arbitrary universe, the rank `n` and both block
shapes are arbitrary, and `w` is any permutation of `Fin n`. There is no
minimal-representative hypothesis. Rank zero and shapes with no allowed entries
are included by the same definitions.

## Definitions and the actual subgroup

`CorrectionAllowed B C w a b` is the proposition

```
blockIndex B a < blockIndex B b ∧
blockIndex C (w a) ≤ blockIndex C (w b).
```

`CorrectionEntry B C w` is the finite subtype of `Fin n × Fin n` satisfying this
predicate. Its decidability is supplied explicitly, so the subtype inherits a
`Fintype` instance. The coordinate space is the ordinary function space
`CorrectionEntry B C w → R`, with its product topology when `R` has a topology.

`correctionSubgroup B C w R` is an abbreviation for the existing ambient
intersection

```
intersectionSource (B.unipotentSubgroup R) (C.parabolic R)
  (permutation n R w).
```

The declaration `intersectionSource` lives in `Langlands.Geometric` in
`WeylDefinitions`; it also resolves from the child namespace `Geometric.General`
used by intersection consumers. Its membership is precisely membership in `U`
and membership of `g h g⁻¹` in `Q`. This module introduces no new group model.
It does not identify this subgroup with the radical of an intersection parabolic.

## Construction of the inverse matrix

`correctionExtension B C w R X` extends a coordinate function `X` by zero to all
matrix positions. `correctionExtension_allowed` evaluates it at an allowed
position; `correctionExtension_eq_zero` evaluates it outside the allowed set.
`correctionBlocks` reads this extended matrix at the standard indices of each
strictly upper rectangular block of `B`.

`correctionMatrix B C w R X` applies the published `B.radicalMatrix` to those
blocks. This is an actual unit of the matrix ring. The imported construction
builds a block upper triangular matrix with identity diagonal blocks, proves its
determinant is one, and uses its adjugate as inverse before reindexing to `Fin n`.
Thus invertibility is constructed, not assumed as part of the coordinate data.

`correctionMatrix_val` proves that its underlying matrix is exactly

```
1 + correctionExtension B C w R X.
```

The proof writes each index using `B.indexEquiv` and uses the published upper,
diagonal, and lower entry formulas for `radicalMatrix`. It does not assume that
`indexEquiv` preserves the order of the numerical indices.

`correctionMatrix_mem` proves membership in the actual full subgroup. Membership
in `U` follows from the published radical matrix's parabolic zeros and identity
diagonal blocks. To prove membership of the conjugate in `Q`, the proof uses
`permutation_conjugate_entry`: its entry at `(w a, w b)` is the original entry
at `(a, b)`. If the target blocks decrease, this is an excluded position, and the
identity contribution also vanishes since `a ≠ b`.

Conversely, `correctionSubgroup_entry_not_allowed` proves that every subgroup
element has the identity matrix entry at any position outside the allowed set.
Below a source block it is zero by parabolic membership; inside a source diagonal
block it is the identity by unipotent membership. Above a source block, exclusion
means a strict decrease in permuted target blocks, so the entry is zero by the
conjugate's parabolic membership.

## Equivalence and entry formulas

`correctionCoordinates B C w R` is the equivalence

```
correctionSubgroup B C w R ≃ (CorrectionEntry B C w → R).
```

Its forward map reads `h.val ab.1.1 ab.1.2` literally. Its inverse is
`correctionMatrix X` with the proved subgroup membership. The two inverse laws
follow entrywise from `correctionMatrix_val` and
`correctionSubgroup_entry_not_allowed`. This is an equivalence of types, not an
isomorphism to the additive coordinate group.

The public formulas are:

- `correctionCoordinates_apply`: forward coordinates are the actual entries;
- `correctionCoordinates_symm_val`: the inverse is `correctionMatrix`;
- `correctionCoordinates_symm_entry`: at every `(a,b)`, the inverse entry is
  `if a = b then 1 else 0`, plus `correctionExtension X a b`;
- `correctionCoordinates_reconstruct`: the underlying matrix of every subgroup
  element is identity plus the extension of its coordinates;
- `correctionCoordinates_one` and `correctionCoordinates_symm_zero`: identity and
  zero coordinates correspond.

Together with the two extension formulas, the inverse entry formula gives `X`
at allowed positions, one on the matrix diagonal, and zero at all remaining
positions. A diagonal position is never allowed because source-block increase
is strict.

## Multiplication and strictly smaller gaps

`correctionCoordinates_mul` states the actual entry formula

```
coord(u * v)(a,b) = coord(u)(a,b) + coord(v)(a,b)
  + ∑ k : Fin n, extend(coord(u))(a,k) * extend(coord(v))(k,b).
```

It follows by reconstructing both matrices as identity plus extension and
expanding their product. No integral-domain hypothesis is needed.

`CorrectionIntermediate B C w ab` is the finite subtype of indices `k` for which
both `(a,k)` and `(k,b)` are allowed. `correctionExtension_mul_ne_zero` proves
that a nonzero cross term implies both positions are allowed; this uses only the
zero-extension formulas. Splitting the full finite sum into this subtype and its
complement gives `correctionCoordinates_mul_allowed`, whose sum is explicitly

```
∑ k : CorrectionIntermediate B C w ab,
  coord(u) ⟨(a,k), k.property.1⟩ * coord(v) ⟨(k,b), k.property.2⟩.
```

`correctionCoordinates_symm_mul_symm` is the same restricted-sum formula applied
directly to coordinate functions `X` and `Y` and their reconstructed elements.

`correctionGap B C w ab` is the natural-number difference
`(blockIndex B b).val - (blockIndex B a).val`.
`correctionIntermediate_gap` proves that both allowed positions of every
intermediate term have gap strictly smaller than that of `ab`: the defining
inequalities give `B(a) < B(k) < B(b)`, and natural-number arithmetic proves both
strict gap bounds. `correctionExtension_mul_gap` packages this conclusion for any
nonzero extended cross term. These are the finite triangular multiplication facts
needed by a subsequent translation argument. This module makes no Haar-measure,
translation-invariance, or scaling assertion.

## Actual inherited topology

For any `[TopologicalSpace R]`, `continuous_correctionCoordinates` proves
continuity of the forward map by composing the existing continuous matrix-entry
maps with the actual subgroup inclusion. `continuous_correctionExtension` is
entrywise continuity of a fixed coordinate evaluation or a constant zero;
`continuous_correctionBlocks` reads the corresponding entries.

With the additional hypothesis `[IsTopologicalRing R]`,
`continuous_correctionMatrix` composes `continuous_correctionBlocks` with the
published `continuous_radicalCoordinates_symm` and the two subtype inclusions.
The imported inverse continuity proves continuity into the units topology by
checking both the matrix and its adjugate inverse. It requires neither a field
nor continuity of inversion on the whole ring. The resulting map lands in the
actual ambient general linear group, with its existing topology.

`continuous_correctionCoordinates_symm` then uses the actual subgroup subtype
constructor. Thus `correctionCoordinatesHomeomorph B C w R` is a homeomorphism
from the actual inherited subgroup topology to the finite product topology. No
new topology on the subgroup is chosen. The `_apply` and `_symm_apply` formulas
identify its maps with those of the equivalence. The arbitrary universe of `R`
is retained throughout.

## Internal provenance

This is a derived implementation from the existing Library definitions and
proved matrix formulas. Its direct imports are
`Langlands.Group.GL.BlockUnipotentCoordinates` and
`Langlands.Representation.Geometric.StandardIntersectionsProof`; the latter
supplies `blockIndex`, the existing intersection, and the membership and
permutation-entry formulas through its imports. The restriction of the
rectangular radical coordinates to this zero pattern, the explicit equivalence,
the topology proof by composition, and the scalar multiplication and gap formulas
are proved in this pair. No external source is claimed to state this coordinate
construction, and no new source assertion or unproved matrix hypothesis is used.
Existing Library pairs are unchanged.
