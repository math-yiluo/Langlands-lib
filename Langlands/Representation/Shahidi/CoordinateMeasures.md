# Coupled scalar, row and matrix coordinate measures

This derived prerequisite records the coordinate part of Shahidi's measure
normalization in *Fourier transforms of intertwining operators and Plancherel
measures for GL(n)* (1984), printed pages 76–77, measure items 2, 3 and 5.
The registered original is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
Printed page 82 explicitly distinguishes the matrix measure from a self-dual
matrix measure. That distinction is retained here.

`matrixCoordinateMeasure da` is the nested finite product of the supplied
additive Haar measures `da i j`, one for every entry of the actual rectangular
matrix space. The generic construction allows zero rows or columns and
possibly different measures at each entry. Sigma-finiteness of every scalar
measure gives sigma-finiteness and finiteness on compact sets of the product.
With measurable addition, the product is an additive Haar measure. These
properties reuse the published row-product instances and Mathlib's product
measure instances. The box formula follows by applying the finite-product
formula twice. For a constant family this is definitionally the published
`RankinSelberg.rectangularMeasure`.

`matrixColumnMeasure da j` is the finite product of the scalar factors in
column j. It is a factor measure, not a projection pushforward of the full
matrix measure: integrating out other coordinates of infinite total mass
would not produce this measure. Its box formula is the row-product formula.
`matrixColumnMeasure_eq_rowCoordinateMeasure` proves that equality of the
individual scalar column measures gives equality with the supplied row
product, by equality of the families under `Measure.pi`.

For a positive square rank n+1, `IsCoordinateMeasureCompatible` is the
following concrete Prop-valued relation on an absolute value, a unitary
additive character, actual multiplicative measures on the field units and
on GL_(n+1), and the row and matrix families of additive Haar measures:

1. The first row-coordinate measure is the actual weighted pushforward
   `fieldMeasureFromUnits abv dzStar`, namely dz = |z| d*z extended to F.
2. The whole row product is self-dual for the conjugate-character dot-product
   Fourier kernel. It uses `IsRowSelfDualMeasure (psi.scale (-1))`, including
   integrability of the second transform and inversion on Schwartz–Bruhat
   functions. The published character-translation identity identifies this
   with the source's conjugate kernel while preserving the Library's
   plus-sign Fourier convention.
3. The whole matrix product equals the actual weighted pushforward
   `matrixMeasureFromGeneralLinear (n+1) abv dgStar`, namely
   da = |det a|^(n+1) d*a extended by zero on the singular matrices.
4. Each scalar factor in the first matrix column equals the corresponding
   row-coordinate measure. The source's one-based indices are translated
   to zero-based `Fin` indices.

These equations concern the supplied actual measures. The relation does not
assert that any tuple exists. Its measure inputs on the two multiplicative
groups are unbundled measures; the additional Haar, local-field, valuation
and absolute-value normalization hypotheses belong to a later complete
measure system. The relation itself is meaningful over a topological field
with measurable structures on the field and the two multiplicative groups.
The matrix and row spaces carry their coordinate product measurable structures;
Borel compatibility is not needed just to define this relation. No choice of a measure
tuple, group measure or Fourier normalization is made here.

The intrinsic lemmas show that the top-left scalar measure equals dz, that
the first-column factor equals the chosen row product, and consequently that
this column factor satisfies the prescribed row self-duality. The first
identity composes two measure equalities; the second uses equality of
coordinate products; the third rewrites the self-duality hypothesis using
that equality. They do not infer self-duality of each scalar coordinate,
equality of all scalar factors, or self-duality of the matrix measure.

This is the coordinate portion of the equal-rank construction, not the
complete suitable-measure relation for Theorem 5.1. It leaves the pairing
and quotient construction of item 1, the compact-volume choice of d*z in
item 2, the compact-subgroup normalization of dk in item 3, the Iwasawa
compatibility of item 4, the common lower-radical measure of item 6 and the
upper-radical transport of item 7 to further units. It also leaves the
unequal-rank normalization and the comparison theorem open.
