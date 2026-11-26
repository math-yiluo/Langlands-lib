# The positive scalar realization of the general-linear adelic quotient

Let `F` be a number field and `n > 0`. The existing adelic point homeomorphism
`GeneralLinearGroupPoints.adelicHomeomorph` sends the canonical split centre
of the actual `GL_n` group scheme onto the image of `PositiveRealIdeles.full F`
under `AdelicGL.scalar F n`. These are the matrices `a I_n` for one positive
real parameter at all infinite places, with finite component one. The same
homeomorphism carries the principal rational-point image to the image of the
original `AdelicGL.rational F n`.

`AdelicGL.SplitCentreQuotient F n` is the left quotient of the original
adelic matrix group by the join of these two subgroups.
`GeneralLinearGroupPoints.splitCentreQuotientHomeomorph` identifies this
quotient with `RestrictionSplitCentre.CanonicalQuotient` via the matrix map
on representatives. It intertwines positive right translation. The subgroup
used in the matrix quotient is closed.

`splitCentreQuotientMeasure` transports the canonical quotient measure to the
matrix realization. For the Borel measurable structure on the matrix group,
`splitCentreQuotientMeasure_isCompatible` gives the Weil formula with the
ambient Haar measure and the combined split-centre and principal subgroup Haar
measure transported by their corresponding continuous group equivalences.
Thus the two realizations have the same quotient normalization. The measure is
finite by the general reductive finite-volume theorem.

## Construction

The scalar torus of positive-rank `GL_n` is a split component by
`GroupScheme.GeneralLinear.scalarTorus_isSplitComponent`. The canonical split
centre agrees with its positive image by
`RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup`. On the source
multiplicative group, the identity character evaluates to the corresponding
idele, and every other character is an integral multiple of the identity.
The character description of the positive subgroup therefore identifies it
with `PositiveRealTorus.scalarSubgroup`. The scalar-torus computation on
points over test schemes gives the scalar matrix after transport from global
sections to the affine coefficient algebra. The principal subgroup comparison
uses `adelicHomeomorph_rational`. The quotient homeomorphism follows by
transport of the left-coset relation, and
`Langlands.QuotientIntegration.isCompatible_map_equiv` transports the Weil
formula along the same maps.

## Provenance

Getz–Hahn, *An Introduction to Automorphic Representations* (2024), (2.20)
and its `GL_n` example, printed pp. 68–69, and (2.21), printed p. 69, describe
the positive scalar subgroup and its left quotient. The measure convention
here uses the canonical measure of `AdelicRestrictionSplitCentreCanonical`
and its Weil formula. The source is registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
