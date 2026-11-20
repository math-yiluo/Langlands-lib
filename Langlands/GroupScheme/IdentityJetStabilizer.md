# Conjugation stabilizers of actual identity jets

`IdentityJet.stabilizer i n` consists of the points that preserve the order-\(n\) identity neighborhood of the source of `i`, viewed in the ambient group, under conjugation and inverse conjugation on every refinement. For a closed subgroup of a separated group, its order-\(n\) jet is the scheme-theoretic intersection of the subgroup and the order-\(n\) jet of the ambient group. The proof uses the actual jet pullback square to give the intersection on literal points of each test.

Every conjugation preserves the ambient jet. The proof changes the base to the test scheme, uses the functorial jet map of the resulting inner automorphism, and transports membership back through the jet pullback square. Smaller ambient jets factor through larger ones because the defining ideal powers decrease with the order. The intersection description then gives a decreasing sequence of subgroup-jet stabilizers, each containing the normalizer of the subgroup. The stabilizer also commutes with arbitrary base change when the source group is separated, by the base-change square for the source jet.

These are internal consequences of the scheme-level jet pullback and stabilizer constructions. They supply the comparison between the jet normalizers in Raynaud's argument for SGA 3, Exposé XV, Theorem 5.2.

The inclusion over the base is `IdentityJet.overInclusion` from `IdentityJetConjugationAction`.

The containment proof uses the cartesian square for a closed subgroup from [Functoriality of identity jets](IdentityJetFunctorial.md). The jet map and its inclusion and projection laws come from `IdentityJetSeparatedBaseChange`.
