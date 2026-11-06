# Normalizer reflection in central-isogeny torus squares

This internal derived result proves normalizer reflection for a central isogeny
`q : G → H` in a commuting square `i ≫ q = f ≫ j`, where `i` is monic, its source
is a field torus, and `f` is flat, surjective and quasi-compact. No reductivity
or smoothness of the ambient groups is assumed. The normalizers use all test
schemes and all refinements, including nonreduced schemes.

The proof uses the published finite exponent of the central kernel. If a point
maps into the range of `j`, an fpqc pullback along `f` lifts its image to a torus
point. Their difference is central and killed by the fixed exponent `N`, so their
`N`th powers agree. Membership in the range of the monomorphism `i` descends
along the cover. Next, any torus point acquires an `N`th root on the fpqc cover
obtained by pulling back multiplication by `N` on the torus. Apply the first
argument to its conjugate and descend again. Doing this for both conjugations
proves normalizer reflection. The file also gives composition and identity
lemmas for the published reflection predicate.

This is an internal proof for the maximal-torus isogeny reduction, derived from
`CentralIsogeny/KernelTorsion`, `Torus/Multiplication` and the effective-epimorphism
subgroup descent in `SubgroupFunctor/FpqcDescent`. It introduces no additional
source assertion.

`CentralIsogenyTorusNormalizerReflectionStatement` names exactly the universally
quantified reflection assertion proved in this file;
`centralIsogenyTorusNormalizerReflection` proves it.
