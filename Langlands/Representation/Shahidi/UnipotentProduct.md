# The upper-unipotent product in measure item 1

This unit implements the ordered product of the smaller upper-unipotent group
and the last-column subgroup used in Shahidi's measure item 1. It constructs
actual mutually inverse coordinate maps, proves their continuity, and transports
the whole product measure to the full upper-unipotent group.

## Source and scope

The original is F. Shahidi, *Fourier transforms of intertwining operators and
Plancherel measures for GL(n)*, American Journal of Mathematics **106** (1984),
67–111, registered as `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
Printed page 75, measure item 1, defines the last-column subgroup of the upper
unipotents and specifies the product measure `dn₁ dn₂`, with the smaller
upper-unipotent group first. Printed page 76 uses the resulting choices when
composing the smaller group measure with the quotient measure.

Our smaller rank is `n`, so the full group here is `N_(n+1)`. The field is an
arbitrary field for the algebraic constructions, and a topological field with
continuous ring operations for the homeomorphism. The definitions and elementary
proofs also cover `n = 0`; this is not a generalization of the paper's analytic
existence theorems to new representations or fields.

The constructions are derived infrastructure for the paper's displayed measure
prescription. No proof of Haar invariance, existence of all compatible choices,
or the full suitable-measure system is claimed by this unit. In particular,
`IsUnipotentProductMeasure` allows zero input measures. Nonzero regular Haar
hypotheses and the pairing and quotient compatibility equations belong to the
later full system.

## Actual group coordinates

`lastColumnUpper x` is the existing `lastColumnUnipotent n x`, now proved to
belong to `GeneralLinear.upperUnipotent (n+1) F`. Its upper-left block is the
identity, its last column above the diagonal is `x`, its bottom row before
the diagonal is zero, and its last diagonal entry is one. These four entry
identities are proved from the published block-unipotent construction.

`upperLeftUnipotent u` is the actual insertion `Bruhat.insert (Fin.last n)`:
its matrix is `diag(u,1)`. The proof of membership uses the published
upper-triangular insertion theorem and the diagonal entry equations.

The map `unipotentProduct` is

```text
(u,x) ↦ diag(u,1) · [[I,x],[0,1]] = [[u,u x],[0,1]].
```

The upper-left block and last-column identities are proved by expanding matrix
multiplication and separating the last summand. The factor order matters: the
column coordinates are not the entries of the product's last column.

`unipotentUpperLeft` takes the actual upper-left block of a full unipotent.
Its inverse is the upper-left block of the inverse full matrix. The two inverse
identities follow from matrix multiplication: the extra summand vanishes because
the relevant bottom-row entry is zero. Upper triangularity and unit diagonal
are inherited entry by entry.

`unipotentProductCoordinates` sends a full unipotent with block and column
`(u,y)` to `(u,u⁻¹ y)`. The two recovery theorems prove both compositions equal
the identity. Their last-column steps use associativity of matrix-vector
multiplication and the actual inverse identities. Their remaining entries use
the proved block identities and unipotent bottom-row equations.

Thus `unipotentProductEquiv` is a bijection, and
`unipotentProductHomeomorph` is a homeomorphism. Continuity of insertion and
block extraction is proved entrywise for both matrices and inverses, using the
units topology. The column coordinate uses continuous matrix-vector
multiplication. This is a homeomorphism of spaces, not a claim that the direct
product group law models the semidirect multiplication law.

## Measure equation and proved transport laws

For supplied measures `dn₁` on `N_n` and `dn₂` on `F^n`,
`unipotentProductMeasure dn₁ dn₂` is

```text
Measure.map unipotentProduct (dn₁.prod dn₂).
```

`IsUnipotentProductMeasure dn₁ dn₂ dn` is the Prop-valued equation identifying
`dn` with this pushforward. The bare equation requires only the displayed
measurable structures. The transport theorems additionally require the given
product measurable structure and the full unipotent measurable structure to
be Borel structures for their actual topologies.

`map_unipotentProductCoordinates` recovers the whole product measure. Its proof
composes the measurable pushforwards and applies the proved inverse identity.
`isUnipotentProductMeasure_iff` characterizes the defining equation by this
recovery equation, using the other inverse identity for the reverse direction.
No infinite-measure marginal under a projection is substituted for a factor.

`unipotentProductMeasure_ne_zero_iff` equates nonzeroness of the transported
measure with nonzeroness of the product. The regularity theorem assumes
regularity of that product and transports it through the homeomorphism.
The integrability and complex integral identities are the ordinary change of
variables laws for its measurable equivalence; their right sides integrate
over the whole product. No unconditional iterated-integral or convergence
claim is made.
