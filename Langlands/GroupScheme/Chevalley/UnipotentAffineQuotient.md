# Affine homogeneous quotients from unipotent vector orbits

This internal construction combines `Chevalley.exists_closed_affine_vector_orbit`
with `SchemeAction.quotientOfClosedAffineOrbit`. Worker 362 authored this bridge
from those existing constructions. It retains the exact proposition
`UnipotentAffineOrbitClosedStatement` as an explicit input and does not prove
Kostant–Rosenlicht.

`HomogeneousQuotientFromEmbedding.AffineHomogeneousQuotient` pairs the existing
homogeneous-quotient bundle with affineness of its underlying scheme. It adds no
new quotient axiom: the contained bundle already has a separated, locally finite
type, quasi-compact scheme, a smooth surjective quasi-compact projection, and
exact right-coset fibers on every relative scheme test.

`Chevalley.unipotentAffineQuotient` works over every algebraically closed field
in an arbitrary universe. Its ambient group is smooth, affine and unipotent;
its specified subgroup is closed, smooth and unipotent. Connectedness and
normality are not assumed. The vector-stabilizer construction supplies a finite
matrix representation and a coordinate-vector orbit with precisely the
subgroup's all-test coset fibers. The supplied closed-orbit proposition makes
that orbit closed. The vector scheme is the spectrum of a polynomial ring in
finitely many variables, hence affine and locally of finite type. Applying the
closed-affine-orbit construction produces the actual schematic image with the
stated quotient geometry and affineness. Classical choice selects such a bundle.

This unit does not put a group structure on the homogeneous quotient, descend
it to an arbitrary field, or establish the host ordered-product proposition.
