# Quadratic cover vanishing for quasi-split inner type E₆

`NumberFieldTotallyComplexInnerTypeE6QuadraticVanishingStatement` says that every cocycle on a quadratic Galois cover of a totally complex number field for a quasi-split, simply connected inner group of type E₆ is trivial. The type and trivial star action are expressed on the supplied actual Tits index.

Quasi-splitness and the inner star condition give a split maximal torus. The maximal split torus of the supplied index is then a maximal torus by rational conjugacy, so every vertex is distinguished. Form the actual pure twist of the cocycle. The quadratic splitting argument for inner E₆ gives its isotropy, and isotropy gives the short-arm marking of its index.

Matching the two branch lines puts the cocycle in the branch centralizer on a finite Galois refinement. The derived group's Cartan diagram is A₅, and its star action is trivial because its torus lies in the split ambient torus. The inner type A Hasse kernel and local vanishing of simply connected cocycles over a totally complex number field give vanishing on the derived group. The split cocenter quotient gives vanishing for the centralizer and descent to the original cover. The lemma `Cocycle.isTrivial_of_splitE6_isotropicTwist` performs this reduction for any finite Galois cover of a split E₆ group with an isotropic pure twist.

This proves the inner degree-two case in Platonov and Rapinchuk, *Algebraic Groups and Number Theory*, §6.8, Theorem 6.29, Proposition 6.22 and Lemma 6.31, pp. 378–382. The proof uses the Weyl obstruction to negation for the quadratic isotropy step. [Chapter 6](https://www.sciencedirect.com/science/article/pii/S0079816908620711)
