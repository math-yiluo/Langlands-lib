# Recovering homogeneous quotients from their sheaf

This derived adapter recovers the actual scheme quotient from a representation
of the canonical coset sheaf. It assumes a smooth affine ambient group, a smooth
monomorphic subgroup and a separated representing scheme over the base.
Transporting the canonical transformation through the representation defines the
scheme projection. A pullback square transfers its smoothness and surjectivity.
The componentwise injectivity of the representation transfers exactly the full
coset fibers on every scheme test.

Local finite presentation descends from the ambient group along the smooth
surjective projection. Quasi-compactness of the structure map follows by taking
the continuous surjective image of the compact preimage of each compact base
open. Separatedness of the target then gives quasi-compactness of the projection.
These data produce the full `HomogeneousQuotient` structure on the supplied
representing scheme.

For an affine fppf cover between affine bases, a supplied quasi-affine local
homogeneous quotient represents the restriction of this sheaf by
`HomogeneousQuotientSheaf.representableBy_baseChange`. The actual-fppf
representability descent theorem supplies a quasi-affine global representative,
which is separated. The preceding construction then returns an actual
quasi-affine homogeneous quotient, smooth over the base by the published
smoothness descent theorem. No additional literature claim is introduced.
