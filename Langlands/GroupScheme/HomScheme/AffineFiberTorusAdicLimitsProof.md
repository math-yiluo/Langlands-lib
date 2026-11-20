# Adic effectivity of closed tori with affine ambient fibres

`AffineFiberClosedToriAdicEffectivityStatement` says that the presheaf of actual closed torus subgroups satisfies `AdicLimits` when the ambient group is smooth, separated and quasi-compact with affine residue fibres. Over a complete Noetherian local test ring, every compatible family of such subgroups on the maximal-ideal thickenings lifts to a unique closed torus subgroup on the test scheme.

The proof applies `affineFiberTorusAdicLimits_of_homEffectivity`. The ambient hypotheses persist after pulling back to the complete local test. Surjectivity of `Adic.affineFiberTorusAdicHom` then provides the homomorphism required by that comparison, which recovers the closed subgroup and its restrictions.

This derives the adic limit condition of SGA 3, Exposé XV, Proposition 8.1(i) from the Hom comparison in (i bis) using the affine-fibre case of Corollary 4.4. Raynaud formulates Proposition 8.1 over a locally Noetherian base. The Lean proof makes all comparisons after pulling back to each complete Noetherian local test, so the ambient base can be arbitrary. The registered source `sga3-expose-xv-raynaud-2008` is the Gille–Polo recomposition of 1 December 2008, recomposed pp. 260 and 288–289, PDF pp. 28 and 56–57.
