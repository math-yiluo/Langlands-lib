# Actual rank-one centralizer cell data

This internal construction combines the actual relative cocharacter centralizer,
its lifted root parametrizations and fieldwise root comparison with the
arbitrary-ring open-cell theorem. It does not assert a new correspondence with
external literature.

Scalar equivariance of an actual root parametrization gives equivariance on every
point of the additive group: every such point has a scalar coordinate.
`LocalRankOneCell.cellData` packages opposite parametrizations, the split torus,
their actual character weights and the open triple multiplication into
`RingRootCell.CellData`. Its assumptions include reductivity, fibrewise maximality,
positive exponent pairing and exact opposite-root support on every supplied
field algebra.

`splitTorus.RelativeCocharacterCentralizer.cellData` applies this construction to
the actual represented centralizer. It uses the lifted opposite root maps and the
inherited torus, reductivity and fibrewise maximality. A fibrewise root datum and a
supplied generic annihilating exponent give the required exact two-root support.
The positive exponent is supplied. Over a local ring `corootCellData` uses the
given root's coroot: its integer pairing is two, as checked on the residue field.

These data contain the actual centralizer and its maps. No abstract replacement
group is introduced. A normalizing Weyl point, its square and its unit-coordinate
decomposition are not constructed here; the full local Isomorphism Theorem remains
open.
