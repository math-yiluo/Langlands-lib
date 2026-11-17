# Simple-root degree cutoffs from supplied linked root coordinates

Let `k` be a field, `G` an actual affine group scheme over `Spec k`, and `p`
a supplied split pinning with a finite indexing of its roots. This internal
unit also assumes integral coroot span and a `SimpleRootCoordinateFamily`.
The family supplies full linked positive and negative simple-root
parametrizations with their actual rank-one relations; its existence is not
asserted. The coordinate space is the entire existing
`canonicalRhoCovariantSubspace`, namely the full left covariant subspace for
the negative-rho character of the actual polarized-rho dynamic subgroup.
No assertion that this subgroup is Borel enters the proof.

For each supplied negative simple map, the unit defines its actual polynomial
curve at a rational translate. The degree-bound results assume that `k` is
infinite. Membership in the whole covariant space gives
positive-root invariance and inverse-power covariance under the simple
coroot. The generic reciprocal-transition degree theorem, applied to the
supplied rank-one relation, therefore bounds the polynomial degree by the
character exponent. This uses the supplied positive full-root image to get
positive-root invariance, without a canonical root-map existence theorem.

Each supplied negative map lifts into the actual opposite dynamic unipotent
representative. Restriction of ambient coordinates preserves the original
curve polynomial, hence preserves the degree bound over an infinite field
at every rational translate.

For the Frobenius-to-left-invariance results, assume that `k` is algebraically
closed and that `q : ℕ` is its exponential characteristic, expressed by
`ExpChar k q`. Let `r m : ℕ` satisfy `m < q^r`. The generic
affine-coordinate translation theorem then turns
right Frobenius-origin invariance into left invariance under every supplied
simple negative map on every relative test scheme. With the same algebraic
closedness and exponential-characteristic hypotheses, exponent `q^r - 1`
meets this cutoff for every `r : ℕ`.

This is a derived supplied-data version of the Library's generic root-curve
and restriction argument. It uses the coordinate restriction definition and
generic covariance laws, and replaces canonical linked-root choices by the
explicit family. It does not use their existence theorem, root-dimension
promotion, or the old Borel/big-cell assembly. No external source assertion
is added.
