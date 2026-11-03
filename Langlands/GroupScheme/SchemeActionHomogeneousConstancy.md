# Fixed sections from proper homogeneous quotients

This internal module extends `SchemeActionOrbitDescent` to actual homogeneous
scheme quotients, whose targets need not carry group structures. Given a flat,
surjective, quasi-compact morphism from a group scheme, an all-test implication
that equal quotient images lie in the same right subgroup coset, and a rational
section fixed by that subgroup on all tests, its orbit morphism factors through
the quotient. The published coset-invariance lemma and fpqc effective descent
`FiniteIndexTransfer.exists_factor` give existence. Classical choice defines
`descendedHomogeneousOrbitMap`; its pullback equation recovers the original
orbit morphism.

Over an algebraically closed field, suppose additionally that the acting group
is connected and reduced, the quotient is proper, and the scheme acted on is
affine. Connectedness passes through the surjective quotient morphism;
reducedness descends through its faithfully flat local maps. The image of the
group identity gives a specified rational point on the quotient. The affine-map
constancy theorem in `ProperConnectedAffineConstancy` therefore makes the
descended orbit constant at this point. The value is the original rational
section, because the identity acts trivially. Pullback proves constancy of the
original orbit, which is equivalent to fixedness on every scheme test.

All constructions use the existing actual morphisms and all-test action and
coset predicates. The quotient is supplied, as are its properness and geometric
hypotheses; this module does not construct a Borel quotient or prove any
normalizer theorem. Its provenance is the published orbit-descent and fpqc
descent interfaces, the reducedness descent lemma in
`GeometricallyReducedOfAlgClosedProof`, and the internal pointed proper affine-map
constancy construction.
