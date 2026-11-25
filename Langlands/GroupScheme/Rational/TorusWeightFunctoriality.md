# Intrinsic weight subgroups and equivariant natural homomorphisms

This derived module proves functoriality of intrinsic weight subgroups over an
arbitrary commutative base ring, allowing different source and target
group-valued functors and corepresenting algebras.

`TorusAction.IsEquivariant` is the proposition that an actual natural group
homomorphism intertwines two split-torus actions on every coefficient algebra.
`transformationPullback` is the actual algebra homomorphism classifying the image
of the source universal point. Naturality computes all coordinate pullbacks using
this homomorphism. Equivariance makes it preserve every homogeneous character,
and the group homomorphism property makes it preserve identity augmentation.

`map_mem_weightSubgroup_of_equivariant` proves preservation of every intrinsic
weight subgroup for every additive semigroup of characters, on every coefficient
algebra. The proof pulls back a homogeneous component in the target, applies the
source subgroup's defining equations to this homogeneous function, and then uses
augmentation compatibility.

A natural group isomorphism requires only forward equivariance: the module proves
equivariance of its inverse and the membership equivalence
`mem_weightSubgroup_iso_iff`. Thus the description does not depend on a particular
corepresenting algebra or polynomial presentation when an actual equivariant
isomorphism is supplied.

The two `groupSchemeMap` theorems transport preservation and membership equivalence
to the actual represented closed subgroup functors on every scheme test. They use
the published point comparison over relative global sections, so the test scheme
need not be affine or reduced.

These results apply to supplied actual equivariant maps. They do not construct
parabolic conjugators, prove conjugation equivariance for different canonical face
cocharacters, or supply the overlap and descent data for the finite vector-bundle
filtrations of supplied relative radicals.
