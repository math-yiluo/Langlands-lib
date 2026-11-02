# Infinite and finite factors of the actual adelic point group

Let `F` be an arbitrary number field and `G` an affine group scheme over
`Spec F`. Mathlib's actual adele ring is the product of the actual
archimedean adele ring and the actual finite restricted-product adele ring,
with its existing algebra structure and product topology. This derived
construction specializes `GroupScheme.affinePointsProdHomeomorph` to those
two coefficient algebras. It yields `AdelicGroupPoints.split`, a
multiplicative homeomorphism from the existing actual full adelic point
group to the product of the existing infinite and finite point groups.
No replacement point carrier or topology is introduced.

The maps `infinite` and `finite` are the actual unital coefficient
projections. The map `pair` is the inverse of this homeomorphism. The
projection and pairing identities, continuity of pairing and the
multiplication formulas follow from that equivalence. `ofInfinite` and
`ofFinite` include the corresponding group factor by pairing it with the
group identity in the other factor. These are continuous group
homomorphisms; they are constructed on group points and do not require a
unital coefficient-ring inclusion into one factor. The factor images
commute, and conjugation on the included finite factor is conjugation by
the finite projection. The implemented proofs apply the product
homeomorphism and use componentwise group operations.

For the actual general linear group scheme, naturality of the existing
scheme-point/matrix comparison identifies both projections with
`AdelicGL.infinite` and `AdelicGL.finite`. This proves the commuting
product-decomposition formula. Applying the original matrix product
homeomorphism then identifies pairing with `AdelicGL.pair`, and hence
identifies both included factor homomorphisms with `AdelicGL.ofFinite`
and `AdelicGL.ofInfinite`. Thus the formulas use the original matrix
spaces and their original factor maps.

The provenance is the universal property of the two coefficient algebras
and the already constructed actual-point comparison. No finite-type or
reductivity hypothesis is needed. This result supplies the factor maps for
finite-level function constructions; it asserts no archimedean smooth
structure, restricted-product description of local group points, quotient
measure, reduction theorem or finite-volume conclusion.
