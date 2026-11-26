# Dimensions of irreducible representations of wild inertia: proof

`Langlands.Henniart.wildClassRankPrimePower` proves
`WildClassRankPrimePowerStatement.{uK, uW}`: for every prime `p`, every p-adic
field `K` and every class `c` in `WildClasses K`,
`openKernelIrreducibleRank _ c = p ^ a` for some `a`.

The proof applies `PPowerOpen.rank` (module
`Langlands.Representation.Clifford.PGroup`) to the wild inertia subgroup
`weilWildInertia K` of the Weil group, which is compact
(`WildInertia.compactSpace_weilWildInertia`) and has the `p`-power property
(`WildInertia.pPowerOpen_weilWildInertia`, module
`Langlands.Correspondence.HenniartWildInertia`).

In words: an open kernel contains the elements of wild inertia that act
trivially on a suitable finite Galois subextension `L / K`. The image of wild
inertia in `Gal(L/K)` is the first lower ramification group, a finite
`p`-group (J.-P. Serre, *Local Fields* (1979), registered as
`serre-1979-local-fields`, IV §2, Corollary 3 to Proposition 7, printed
pp. 67–68). So the representation factors through a finite `p`-group, and
its dimension is a power of `p`. The Lean proof of the last fact uses an
induction along normal subgroups of index `p` and the Clifford rank formula
`finrank_of_over`, in place of the divisibility of the order by the degree in
J.-P. Serre, *Linear Representations of Finite Groups* (1977), registered as
`serre-1977-linear-representations`, §6.5, Corollary 2 to Proposition 16
(printed p. 52).
