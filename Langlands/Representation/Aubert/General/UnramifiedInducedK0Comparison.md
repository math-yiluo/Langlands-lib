# Untwisting a dense normalized induced character comparison in exact K0

This internal derived adapter combines the actual normalized induction and
character constructions. It supplies a conditional exact-class comparison, with
the distribution comparison on the dense family explicitly retained.

For a locally compact nonarchimedean group, a semidirect decomposition of a
parabolic subgroup into its Levi subgroup and closed radical, and any indexed
family of positive norm characters on that Levi,
`normalizedUnramifiedInductionTrivialTwistIso` applies
`normalizedInductionFunctor.mapIso` to `SmoothRep.twistOneIso`. It is a genuine
isomorphism from induction of the trivial twist to the original induction.
There is no assumed isomorphism between inductions from different parabolics.

With a Borel measurable structure, Hausdorff topology, a left invariant measure
finite on compact sets, compact left quotient, continuous Levi projection and
admissible coefficient representation,
`normalizedUnramifiedInductionDistribution_one` identifies the genuine
distribution at the trivial unramified parameter with that of the original
normalized induction. The proof converts the constructed isomorphism by
`SmoothRep.equivOfIso` and applies
`Character.distribution_eq_of_equivariant`. The actual induced
admissibility proof is supplied by the published
`normalizedInductionFunctor_obj_isAdmissible` from
`RationalInductionDualityReduction`.

`normalizedInductionClass_eq_of_dense` compares two actual decompositions
sharing the same Levi and norm family. Both parabolics and radicals are closed,
both Levi projections continuous, and both left quotients compact. Every norm
character is continuous, and both coefficient representations are admissible.
The induced objects have explicitly supplied finite-length proofs.
For a regular Haar measure, also assume every finite-length smooth ambient
representation in their carrier universe is admissible. Equality of the genuine
induced distributions on an explicitly dense set of unramified characters then
implies equality of the original exact finite-length K0 classes.

The proof applies
`normalizedUnramifiedInductionDistribution_eq_of_dense`, evaluates its result at
the trivial character, uses the two preceding untwisting formulas and applies
`Character.ofRepresentation_eq_iff_distribution_eq`. The last theorem uses the
published `exactK0CharacterRealization` and `exactK0CharacterInjectivity`.
Consequently character independence and the actual Jordan–Hölder description of
the exact quotient enter through those published proofs. The coefficient,
group and norm-index universes are independent; induced carriers have universe
`max uG uV`. The K0 is the quotient by all actual short exact sequences.

No reductive-group genericity assertion, nonzero polynomial witness,
finite-length admissibility theorem or unconditional Weyl conjugacy is proved
here. The input comparison is equality of actual distributions.
