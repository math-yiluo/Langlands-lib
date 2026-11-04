# Reduction of the central-isogeny root-datum theorem to geometric inputs

This internal assembly uses the published proof
`centralSurjectionMaximalSplitTorusImage` to discharge the maximal-image premise
of the existing torus-restriction construction. It adds no external source claim.
It preserves arbitrary field universe, all characteristics, imperfect fields and
possibly inseparable central isogenies with their full scheme-theoretic kernels.

`IsCentralIsogeny.isIsogeny_torusRestriction` proves that the supplied commuting
restriction between split maximal tori of connected reductive groups is finite,
flat and scheme-surjective. Its proof applies
`isIsogeny_torusRestriction_of_maximalImage` to the published maximal-image
theorem. That adapter constructs the split fppf image of the restriction.
Maximality of this image makes its inclusion in the supplied target torus an
isomorphism. The projection is flat and surjective; ambient finiteness and the
closed torus inclusions give finiteness of the restriction. No differential
surjectivity or smoothness of the kernel enters this argument.

`IsCentralIsogeny.torusRestrictionQuasiInverse` constructs an actual reverse torus
homomorphism and a nonzero integer such that both composites are multiplication
by that integer. It specializes the existing quasiinverse construction by
discharging the same maximal-image premise.

`IsCentralIsogeny.rootDatumHomOfMaximalTori` specializes the actual
`rootDatumHomOfComparisons` construction to these supplied split maximal tori.
The source and target root-index types have independent universes. The
torus-isogeny premise is now proved. The following inputs remain explicit:

- both all-test-scheme self-centralizer equalities;
- equality of the two ambient Lie dimensions;
- finiteness of the full target normalizer image on its entire character lattice.

`centralIsogenyRootDatumHom_of_geometric_inputs` reduces the complete unchanged
`CentralIsogenyRootDatumHomStatement` to three input families:
`MaximalTorusCentralizerStatement`, `SplitTorusWeylImageFiniteStatement`, and Lie
dimension invariance for central isogenies of connected reductive groups. It
installs the affine and smooth instances supplied by reductivity, specializes the
three families, constructs the preceding actual Hom, and invokes
`rootDatumHomOfComparisons_spec`.

Consequently the conditional reduction retains every quantifier and conclusion
of the published target: arbitrary supplied root data, actual character pullback
and cocharacter pushforward, both lattice injections, and the ambient isomorphism
criterion. The root and coroot comparisons and the specification are the
published ones described in `RootDatumOfComparisons.md`. This module does not
prove any of the three remaining geometric input families and does not prove
the complete target without them.
