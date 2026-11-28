# Splitting of quasi-split simply connected groups of type \(E_7\)

`QuasiSplitTypeE7SplittingStatement` concerns an affine, locally finite-type
group scheme \(G\) over a field \(K\). Its actual Tits index has simple vertices
numbered by `Fin 7`, with integral Cartan pairings given by `CartanMatrix.E 7`.
If \(G\) is simply connected and quasi-split, it has a split maximal \(K\)-torus.

`quasiSplitTypeE7Splitting` proves this from Cartan rigidity and the absolute
star criterion. `Langlands.CartanE7Root.rigid` forces every permutation of
the numbered vertices preserving the Cartan entries to fix all vertices.
Simple connectedness ascends to the separable closure. The coroot-span
criterion there gives that the simple coroots span the cocharacter lattice
of the supplied split pinning. A root-datum automorphism fixing every simple
index is therefore the identity, by
`InnerTypeANormOneReduction.aut_eq_one_of_simple`. This proves triviality
on the full based root datum, to which `quasiSplitStarCriterion` applies.
