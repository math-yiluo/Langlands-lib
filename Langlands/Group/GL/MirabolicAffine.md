# Affine coordinates for the actual mirabolic matrix group

Authors: Worker 452 (original draft) and Worker 714 (verification,
additional interface lemmas and this description).

This module constructs affine coordinates for the published actual matrix
group `GeneralLinear.mirabolic n F`. Its elements are invertible
`(n+1) × (n+1)` matrices whose final row is `(0,...,0,1)`. The construction
is internal algebra and topology derived from the published matrix geometry
in `Langlands.Group.GL.Mirabolic` and `Langlands.Group.GL.MirabolicRadical`.
It does not transcribe an external source. Its purpose is to expose the
factorization of every mirabolic element through the existing radical
insertion `radicalElement` and standard Levi embedding `levi`.

## Hypotheses

All algebraic declarations use an arbitrary universe `u`, a commutative
ring `F : Type u`, and any `n : ℕ`. This includes `n = 0` and the zero
ring. The topological declarations add only `TopologicalSpace F` for the
two projections. Reassembly and the homeomorphism also assume
`IsTopologicalRing F`. No field, positivity, Hausdorff or local
compactness hypothesis is imposed, and no new topology is introduced.

## Leading block

`linearPart : mirabolic n F →* GeneralLinear n F` is an actual monoid
homomorphism. A private matrix map takes the leading `n × n` block,
indexed by `Fin.castSucc`. Two private lemmas show that this block map
sends `1` to `1` and preserves products. The product lemma expands the
`(n+1)`-term matrix sum with `Fin.sum_univ_castSucc` and uses the fixed
last row of the right factor: its entry under a leading column is zero, so
the extra summand vanishes. No invertibility of the block is assumed.
The inverse of `linearPart g` is defined as the leading block of the
actual inverse matrix `g⁻¹`. The two unit identities follow from the
product lemma applied to `g * g⁻¹ = 1` and `g⁻¹ * g = 1`.

The exported identities are as follows:

- `linearPart_entry`: `(linearPart g).val i j = g.val.val i.castSucc j.castSucc`;
- `linearPart_inv_entry`:
  `((linearPart g)⁻¹).val i j = (g⁻¹).val.val i.castSucc j.castSucc`;
- `linearPart_mul`: `linearPart (g * h) = linearPart g * linearPart h`.

## Final column and multiplication

`columnPart g : Fin n → F` is the final column above its bottom entry,
`columnPart g i = g.val.val i.castSucc (Fin.last n)` (`columnPart_apply`).
The same sum expansion proves `columnPart_mul`. This time it uses the
right factor's bottom-right entry `1`:

```text
columnPart (g*h) = columnPart g + (linearPart g).val.mulVec (columnPart h),
(A.val.mulVec w) i = ∑ j : Fin n, A.val i j * w j.
```

Here `mulVec` is ordinary multiplication of a column vector by a matrix,
with no transpose or dual action.

## Reassembly

`affineMatrix A v` is literally `(radicalElement v).val * levi A`, a
product in the actual mirabolic group, with matrix `[[A,v],[0,1]]`. Its
entries are expanded with the published entry lemmas `radicalElement_first`,
`radicalElement_last`, `levi_first`, `levi_last` and `levi_bottom`:

- `affineMatrix_first`: the leading block is `A`;
- `affineMatrix_last`: the final column above the bottom entry is `v`;
- `affineMatrix_bottom`: the bottom row is the inherited mirabolic row
  `(0,...,0,1)`, read from the subgroup membership of the product.

These formulas give `linearPart_affineMatrix` and
`columnPart_affineMatrix`. `affineMatrix_parts` shows that
`affineMatrix (linearPart g) (columnPart g) = g`. It checks every entry,
splitting each index of `Fin (n+1)` into the last coordinate or a
`castSucc` coordinate with `Fin.lastCases`. The bottom-row entries agree
because both matrices lie in the mirabolic group.

`affineCoordinates : mirabolic n F ≃ GeneralLinear n F × (Fin n → F)`
packages these maps. Its forward map is `(linearPart g, columnPart g)`
(`affineCoordinates_apply`), and its inverse is `affineMatrix p.1 p.2`
(`affineCoordinates_symm_apply`). The multiplication law is exported
in two forms:

```text
affineCoordinates_mul :
  affineCoordinates (g*h) =
    (linearPart g * linearPart h,
     columnPart g + (linearPart g).val.mulVec (columnPart h))
affineMatrix_mul :
  affineMatrix A v * affineMatrix B w = affineMatrix (A*B) (v + A.val.mulVec w)
```

The first combines `linearPart_mul` and `columnPart_mul`. The second
follows from the first by injectivity of `affineCoordinates` and the
reassembly identities. So the product coordinate set carries the
transported affine law `(A,v)(B,w) = (AB, v + A.val.mulVec w)`. The
equivalence is not a group isomorphism with the direct product
`GeneralLinear n F × (Fin n → F)`, and no such claim is made.

## Topology

The mirabolic group carries its published subgroup topology inside the
matrix-unit topology of `GeneralLinear (n+1) F`. `GeneralLinear n F` has
Mathlib's units topology. The coordinate space has the product topology,
with the function-space topology on `Fin n → F`.

For any `TopologicalSpace F`, `continuous_linearPart` is proved with
`Units.continuous_iff`. Value entries are the continuous entry maps
`Mirabolic.entry i.castSucc j.castSucc`. Entries of the inverse are
leading entries of the inverse matrix in `GeneralLinear (n+1) F`. They
are continuous by `Units.continuous_coe_inv` composed with coordinate
evaluations and the subtype inclusion. `continuous_columnPart` is the
continuity of finitely many entry evaluations. Neither theorem assumes
continuity of the ring operations.

Under `IsTopologicalRing F`, `continuous_affineMatrix` follows from the
published `continuous_radicalElement` and `continuous_levi` and from
continuity of multiplication in the mirabolic group.
`affineHomeomorph : mirabolic n F ≃ₜ GeneralLinear n F × (Fin n → F)`
uses `affineCoordinates` as its underlying equivalence, with these
continuity proofs in the two directions. The simp lemmas
`affineHomeomorph_apply` and `affineHomeomorph_symm_apply` record its
two maps.

## Boundary cases and scope

For `n = 0` the column space `Fin 0 → F` and the actual group
`GeneralLinear 0 F` are used directly, with no positivity assumption or
replacement of these boundary objects. Over the zero ring every statement
holds as stated.

This module makes no representation-theoretic or irreducibility
assertion. It supplies no measure, modulus calculation, quotient
null-class transport, Fourier operator, semidirect induction or Hilbert
completion. In particular, this homeomorphism does not prove conullity
for any quotient measure. Such claims need their own explicit measure
hypotheses and later proofs.
