# Descent and uniqueness for relative torus conjugators

Worker 668.

This internal derived unit addresses the elementary parts of the published
`ReductiveIsogenyTorusRigidityStatement`, with the same all-test predicate
`TorusConjugates` already used by `IsogenyAdjointTorusDescent`.

`FppfLocallyTorusConjugate i f F` abbreviates the existence of an fppf cover
of the base on each member of which there is a torus point satisfying
`TorusConjugates i f F`. This is exactly the local-existence clause of the
published statement; the predicate does not assert existence without proof.

`TorusConjugates.difference_mem_center_of_isogeny` proves that two conjugating
torus points have central difference. It uses finite flat surjectivity of `F`
to compare morphisms after a local lift of an arbitrary target point. Equality
of the two conjugation formulas then gives commutation by group algebra. The
centre is tested on every scheme over the given test scheme, so this includes
nonreduced tests and nonsmooth kernels. No reductivity or torus maximality is
needed for this implication.

`torusRestriction_eq_of_fppf_local_conjugates` proves that local conjugators
force equality of the restrictions to the supplied commutative source group.
Only the factorization of the second restriction through the target
commutative group is needed. Conjugation is trivial on its image, and equality
of morphisms descends through the pullback of the fppf cover to the source
commutative group. No assumptions of affineness, nonemptiness, connectedness,
or reducedness are imposed on the base.

`FppfLocallyTorusConjugate.torusRestriction_eq` packages this implication
using the new predicate, choosing a conjugator on each cover member.

The provenance is internal: these are consequences of the definitions and
published fpqc local lifting and fppf descent, corresponding to the elementary
uniqueness and reverse implication in Conrad's Corollary 6.1.15. This unit does
not yet establish existence of local conjugators.
