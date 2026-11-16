# The coroot quotient map on a split big cell

This derived construction continues the split maximal-torus quotient in
Conrad, *Reductive Group Schemes* (2014), Theorem 5.3.1, printed pp.160–163.
The source defines the map on the big cell by discarding its two unipotent
coordinates and projecting its torus coordinate to the quotient by the
coroot-generated subtorus. The present module constructs this actual morphism
and proves its geometry and two translation laws. The use of the Library's
generator-relation framework below is internal.

For any commutative ring `R`, finite coordinate type `I`, and coordinate root
datum `P`, `corootCellProjection R I P m n` is the composite from
`𝔾ₐᵐ × T × 𝔾ₐⁿ` through its torus coordinate to `corootQuotient`.
`comp_corootCellProjection` proves that formula on every scheme test. The cell
unit `(0,1,0)` maps to the identity. `torusCellSection` embeds the coordinate
torus with zero root coordinates, and its composite with the cell projection
is the original `corootProjection`.

When the root index type is finite, `smooth_corootCellProjection` composes two
smooth product projections with the smooth torus projection proved in
`CorootTorusProjectionGeometry`. The omitted factors are vector groups, which
are smooth over `R`. Surjectivity follows because the original surjective
torus projection factors through the torus section of this cell map. These
arguments apply to nonreduced rings and the zero ring as well.

The generic lemmas in `LocalSplitCell` describe trivial root maps, denoted `0`
as homomorphisms of group objects. Their underlying scheme maps have constant
identity value. Ordered products of them are the identity, so their cell
formula is just the torus coordinate. They are equivariant for any prescribed
exponent characters, and Weyl conjugation and the Weyl-family construction
leave them trivial.

`cellCompatible_of_generatorRelations` is a generic consequence of the
published `RightGood` framework. It assumes a reductive source, an open source
cell, an affine target, and the explicit `TorusRelations` and `RootRelations`
between the two cell formulas. The published `hasCellFactors_cellMap` and
`rightGood_cellMap` make each pair of corresponding cell points right-good.
Testing a multiplication relation against its right factor proves the
compatibility on local rings with separably closed residue fields. The
published detection theorem then gives compatibility on every scheme test.
No target open immersion or target reductivity is required.

`torusRelations_corootCellProjection` assumes torus equivariance of the source
root maps and that its cell map is a monomorphism. It applies the generic torus
translation formula with trivial target root maps.
`corootCellProjection_mul_positiveRoot` uses an actual reductive group with a
fibrewise maximal coordinate torus, its fibrewise root datum, a base, actual
parametrizations of all roots, and enumerations of the negative and positive
roots. Over every local test ring, right multiplication by a positive root
point changes only the positive coordinates, by the published positive-cell
theorem. Monicity of the source cell identifies the resulting point, so its
torus coordinate and coroot quotient value are unchanged. The local test ring
may have nilpotents.

The module does not prove the negative-simple-root translation law or full
cell compatibility for the coroot quotient, and does not extend the map to the
ambient reductive group. Those remain separate obligations.
