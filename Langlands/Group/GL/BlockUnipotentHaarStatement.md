# Haar measure in upper block coordinates

Author: Worker 117.

This module states the internal prerequisite
`Langlands.GLBlockUnipotentCoordinateHaarStatement`. It does not prove it.
It imports the published coordinate construction in
[`BlockUnipotentCoordinates`](BlockUnipotentCoordinates.md) without changing it.

For every p-adic field `F`, supplied topological realization `T`, and ordered
block shape `B`, install exactly `T.topology`. Give each strict upper rectangular
block and the actual group `B.unipotentRadical F.Carrier` their Borel measurable
structures. For each upper block pair `i < j`, choose any additive Haar measure
`μ_ij` on the matrix space with `B.size i` rows and `B.size j` columns.

The proposition asserts that the pushforward of the finite product
`Measure.pi μ` along `(B.radicalCoordinates F.Carrier).symm` is a Haar measure
on the actual block radical. The source measurable structure of this map is
the dependent product of the block Borel structures. Its target measurable
structure is the Borel structure of the published radical topology.
The map sends the collection of upper blocks to the corresponding matrix
with identity diagonal blocks and zero lower blocks.

The conclusion `Measure.IsHaarMeasure` includes left invariance, finiteness on
compact sets, and positive measure for every nonempty open set. It does not
assert a new normalization or a measure equality with an arbitrarily supplied
Haar measure. There is no regularity, sigma-finiteness, countability, or
triangular-translation premise in the proposition; these are proof obligations
where needed. The field universe and the block shape are unrestricted.
If there are no strict upper block pairs, the product measure is the unit
Dirac measure on the one-point coordinate space, which transports to the unit
Dirac measure on the trivial radical.

## Internal provenance and proof obligations

This statement isolates the measure-transport step needed for the published
`Langlands.GLBlockModulusHaarStatement`. It is an internal consequence suggested
by the already proved coordinate formulas, rather than a theorem attributed
to external literature.

For a fixed radical element `u`, the published multiplication formula sends
the variable block `X_ij` to

`u_ij + X_ij + sum_{i < k < j} u_ik X_kj`.

The variable inputs in the correction have strictly smaller gap `j - k` than
`j - i`. The separately stated finite triangular translation principle is
therefore a potential route to left invariance of product measure. That
principle still needs its own proof, and applying it requires measurability and
the lower-gap dependence argument. The published coordinate homeomorphism
provides the topological transport, but it does not by itself prove the Haar
properties. Intrinsic p-adic countability and local compactness can supply the
measure-theoretic hypotheses needed for finite products and transport.

This module does not prove Levi-conjugation scaling, rectangular determinant
scaling, Haar uniqueness, or the parent block-modulus statement. Those remain
separate obligations.
