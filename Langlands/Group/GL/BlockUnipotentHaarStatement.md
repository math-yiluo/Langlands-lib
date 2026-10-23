# Haar measure in upper block coordinates

Author: Worker 117.
Proof-status correction: Worker 86.

This module defines the internal prerequisite
`Langlands.GLBlockUnipotentCoordinateHaarStatement` as a `Prop`; it contains
no proof. The separately published
[`BlockUnipotentHaarProof`](BlockUnipotentHaarProof.md) proves this exact
proposition as `Langlands.glBlockUnipotentCoordinateHaarStatement`.
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
triangular-translation premise in the proposition; the companion proof supplies
its auxiliary hypotheses internally. The field universe and the block shape are
unrestricted.
If there are no strict upper block pairs, the product measure is the unit
Dirac measure on the one-point coordinate space, which transports to the unit
Dirac measure on the trivial radical.

## Internal provenance and proof status

This statement isolates the measure-transport step needed for the published
`Langlands.GLBlockModulusHaarStatement`. It is an internal consequence suggested
by the already proved coordinate formulas, rather than a theorem attributed
to external literature.

For a fixed radical element `u`, the published multiplication formula sends
the variable block `X_ij` to

`u_ij + X_ij + sum_{i < k < j} u_ik X_kj`.

The variable inputs in the correction have strictly smaller gap `j - k` than
`j - i`. The published theorem
`Langlands.HarmonicAnalysis.finiteTriangularTranslation` in
[`TriangularTranslationProof`](../../HarmonicAnalysis/TriangularTranslationProof.md)
proves the whole `FiniteTriangularTranslationStatement`, with independent index
and coordinate universes `uI` and `uX`. It preserves finite products of
sigma-finite additive left-invariant measures on dependent additive commutative
groups with measurable addition, provided the correction is measurable and
each component depends only on coordinates of strictly lower rank.

Applying this theorem still requires checking measurability and strictly
lower-gap dependence. `BlockUnipotentHaarProof` checks both: continuity of the
coordinate maps, multiplication and subtraction makes the correction measurable,
and `coordinateCorrection_depends` verifies dependence using the displayed
formula with rank `j - i`. Its closing theorem
`Langlands.glBlockUnipotentCoordinateHaarStatement` supplies
`finiteTriangularTranslation.{0,uF}` to
`glBlockUnipotentCoordinateHaarStatement_of_triangular`, proving the complete
coordinate-Haar proposition. Intrinsic p-adic second countability and local
compactness supply sigma-finiteness of the block Haar measures. The coordinate
homeomorphism transports compact finiteness and positivity, and the proved
triangular invariance supplies left invariance on the radical.

This module does not prove Levi-conjugation scaling, rectangular determinant
scaling, Haar uniqueness, or the parent block-modulus statement. These are
separate results beyond the coordinate-Haar conclusion.
