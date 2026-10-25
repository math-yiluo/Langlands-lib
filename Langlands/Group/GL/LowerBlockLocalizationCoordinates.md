# Actual lower-block localization coordinates

This module is internal coordinate infrastructure extracted from the displayed
matrix in H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg convolutions*, American Journal of Mathematics 105 (1983),
Lemma 9.2, printed pages 454–455 (one-based PDF pages 89–90). The registered
source is `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Both rendered pages were read. The project/source errata locations and bounded
filename search supplied no source-specific erratum for this display; this is
not a claim that no erratum exists elsewhere.

The construction and its intrinsic algebraic and topological laws below are
internal derivations from actual block matrices. They do not assert Whittaker
localization, Fourier inversion, integral comparisons, or a tail-factor theorem.
In particular, this module does not prove the existence of the function or
compact open subgroups in Lemma 9.2.

## Parameters, source convention, and matrix meaning

All declarations are in `Langlands.GeneralLinear`. The coefficient ring is an
arbitrary `R : Type u` with `CommRing R`; in particular the construction applies
to every field in its own universe. The natural numbers `a`, `d`, and `c` may
be zero. In the source specialization they are `a`, `b-a`, and `r-b`, which
are positive when `0 < a < b < r`.

`lowerTriangularSubgroup d R` is the subgroup of actual `GeneralLinear d R`
whose matrix is `Matrix.IsLowerTriangular`. Its membership theorem
`mem_lowerTriangularSubgroup_iff` says precisely that the entry in row `i`,
column `j` is zero whenever `i < j`. Closure under products and inverses uses
Mathlib's block-triangular laws for the reversed order on `Fin d`. This is the
lower analogue of the published `upperTriangularSubgroup`; it has the inherited
subgroup topology, not an abstract carrier equipped with an external isomorphism.

For `g : GeneralLinear a R`, `x : Matrix (Fin d) (Fin a) R`, and
`h : lowerTriangularSubgroup d R`,

```text
lowerBlockLocalization c g x h = [[g, 0, 0],
                                 [x, h, 0],
                                 [0, 0, I_c]].
```

The source writes `M(a × (b-a), F)` near its display. Irrespective of the order
in that terminology, the displayed lower-left block has `b-a` rows and `a`
columns. Lean's first matrix index is the row index: `x i j` is the entry in
middle-block row `i : Fin d` and first-block column `j : Fin a`. The construction
does not transpose this block.

`lowerBlockPair g x h` constructs the first two blocks as a matrix unit on
`Fin a ⊕ Fin d`, then applies the published `reindex finSumFinEquiv`.
`lowerBlockLocalization` applies the published `rankInclusion c`, appending
an identity block. This reuses the `blockSum` API of `Group.GL.RankMaps`.
The Rankin–Selberg `appendIdentity` API recursively appends individual
coordinates and has a positive initial rank; `rankInclusion` is the generic
underlying construction suitable also for zero ranks here.

These raw parameters do not carry a direct-product multiplication making this
chart a group homomorphism. The actual lower-left block in the product of two
such matrices is `x*g' + h*x'`. The Lean chart is an ordinary function.

## Standard consecutive indices

The total rank is `a + d + c`, parsed as `(a + d) + c`. The public embeddings
make all offsets explicit:

| Embedding | Definition | Value as a natural number |
| --- | --- | --- |
| `lowerBlockFirst d c i` | `(i.castAdd d).castAdd c` | `i.val` |
| `lowerBlockMiddle a c i` | `(i.natAdd a).castAdd c` | `a + i.val` |
| `lowerBlockLast a d i` | `i.natAdd (a+d)` | `(a+d) + i.val` |

`Fin.castAdd` preserves the coordinate and extends its bound;
`Fin.natAdd` shifts by the indicated initial rank. `finSumFinEquiv` identifies
these embeddings with the left and right summands, without a permutation of
consecutive coordinates. No reassociation cast is hidden in the chart. A
consumer using `a + (d + c)` must transport the rank along
`Nat.add_assoc a d c`, for example by reindexing with
`finCongr (Nat.add_assoc a d c)`; this preserves each natural coordinate.

The nine simp theorems `lowerBlockLocalization_11` through
`lowerBlockLocalization_33` give every block entry, using exactly these
embeddings. The diagonal entries are those of `g`, `h.val`, and the identity;
the `21` block is `x`; the remaining five blocks vanish. The four
`lowerBlockPair_11`, `_12`, `_21`, and `_22` lemmas give the corresponding
first-stage formulas. Their proofs unfold the index equivalence and use the
published `blockSum` entry laws.

## Inverse and determinant

The private two-block unit is constructed with inverse

```text
[[g^-1,              0],
 [-h^-1 * x * g^-1, h^-1]].
```

Both inverse identities follow by block multiplication and cancellation of the
two diagonal units. `lowerBlockPair_inv` and `lowerBlockLocalization_inv`
identify the inverse with the chart at these new parameters. Thus the latter
also gives all nine inverse block entries by applying the entry lemmas.
`h⁻¹` is inversion in the actual lower-triangular subgroup; the matrix in the
formula is its underlying inverse unit. Multiplication and negation in the
formula are matrix operations with the displayed row and column types.

`det_lowerBlockLocalization` proves

```text
Matrix.det (lowerBlockLocalization c g x h).val
  = Matrix.det g.val * Matrix.det h.val.val.
```

The proof uses invariance of determinant under simultaneous reindexing,
the determinant formula for a lower block-triangular matrix, and determinant
one of the appended identity. No positivity or field hypothesis is needed.

## Coordinate recovery and continuity

`LowerBlockParameters a d R` abbreviates
`GeneralLinear a R × Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R`,
with the product topology when a topology on `R` is given.
`lowerBlockLeading`, `lowerBlockRectangle`, and `lowerBlockDiagonal` are
submatrix projections defined on the entire ambient general linear group;
their codomains are matrices. The three `_chart` lemmas recover respectively
`g.val`, `x`, and `h.val.val`. This gives `lowerBlockLocalization_injective`.

`lowerBlockImage a d c R` is the range of the chart in the actual ambient
general linear group. `lowerBlockRecoverG` and `lowerBlockRecoverH` promote
the leading and middle projections on this image to actual units, with the
second landing in `lowerTriangularSubgroup d R`. Their inverse matrices are
the same diagonal projections of the inverse ambient matrix. The proof that
these are inverse matrices reduces an image point to its parameters and uses
`lowerBlockLocalization_inv` and the recovery lemmas. Lower triangularity
reduces to the original middle-block membership proof.

`lowerBlockCoordinates` collects these two units and the rectangular
projection. `lowerBlockCoordinates_chart` proves recovery of every input
parameter triple; `lowerBlockLocalization_coordinates` proves reassembly of
every point of the image. These concern exactly the chart image and assert no
global decomposition of arbitrary ambient matrices.

For any `TopologicalSpace R`, the following are continuous:

- The three ambient matrix projections, by
  `continuous_lowerBlockLeading`, `continuous_lowerBlockRectangle`, and
  `continuous_lowerBlockDiagonal`.
- The two unit-valued projections on the image, by
  `continuous_lowerBlockRecoverG` and `continuous_lowerBlockRecoverH`.
- The entire recovery map, by `continuous_lowerBlockCoordinates`.

The unit-valued assertions use `Units.continuous_iff`: both the value matrix
and the inverse matrix must be continuous. `Units.continuous_val` and
`Units.continuous_coe_inv`, followed by submatrix projection, provide these
two facts. This does not assume continuity of coefficient-ring inversion.

With the additional hypothesis `IsTopologicalRing R`,
`continuous_lowerBlockLocalization c` proves joint continuity of the chart.
The value matrix depends continuously on the parameters through block assembly;
the inverse matrix does so through the polynomial expression
`-h^-1*x*g^-1`, where the two inverse matrices are already continuous functions
of matrix units. Continuous reindexing and `rankInclusionContinuous` finish
the proof. These hypotheses apply in particular to topological fields; no
extra hypothesis about continuity of inversion on the field is used.
