# Dimensions of irreducible representations of wild inertia

`Langlands.Henniart.WildClassRankPrimePowerStatement.{uK,uW}` says: for every
prime `p`, every p-adic field `K` and every class `c` in `WildClasses K`, the
dimension `openKernelIrreducibleRank _ c` is `p ^ a` for some natural `a`.
`WildClasses K` consists of the isomorphism classes of finite-dimensional
irreducible complex representations, with open kernel, of the actual wild
inertia subgroup `weilWildInertia K` of the local Weil group. The kernel is
open for the subspace topology from the Weil group.

**Derived provenance.** J.-P. Serre, *Local Fields* (1979), registered as
`serre-1979-local-fields`, IV §2, Corollary 3 to Proposition 7, printed
pp. 67–68 (PDF pp. 74–75): the first ramification group of a finite Galois
extension is a `p`-group. In the Library, wild inertia is the subgroup of
automorphisms whose restriction to every finite Galois subextension lies in
its first lower group. An open kernel contains all elements of wild inertia
that fix a suitable finite Galois subextension. Hence the image of wild inertia
is a finite `p`-group. J.-P. Serre, *Linear Representations of Finite Groups*
(1977), registered as `serre-1977-linear-representations`, §6.5, Corollary 2
to Proposition 16, printed p. 52 (PDF p. 60): the degree of an irreducible
complex representation divides the order of the group. This module states
the consequence and proves nothing.
