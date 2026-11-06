# Intrinsic geometric reflections

For a smooth affine group scheme over an arbitrary affine base, a closed
standard split torus, and a point of the reductive geometric identity-component
locus at which that torus is self-centralizing, this file constructs
`GeometricRootReflectionData` for each actual geometric exponent root.
The selected definition is `splitTorus.geometricRootReflectionDataIntrinsic`.
The file also proves that this actual exponent-root set is closed under
negation. All results are uniform in the arbitrary universe `u`.

The construction uses the actual generic cocharacter centralizer already
defined by `RankOneCentralizerDetection`. For an algebraically closed field,
a connected reductive group, a split maximal torus and an actual root, its
generic annihilating cocharacter has a represented smooth connected reductive
centralizer. The torus factors as a maximal torus in that centralizer, and
the chosen root remains a root there. All its roots are pairwise integrally
dependent.

`Dynamic.isCentral_cocharacter_torusFactor` first proves that the defining
cocharacter is central in its actual represented centralizer. On every test
scheme and refinement, the centralizer predicate gives commutation after
composition with the inclusion. Monomorphism cancellation gives commutation
inside the centralizer itself. This proves centrality of the exact factored
cocharacter.

`RankOneCentralizerDetection.exists_nonidentityNormalizer` chooses a proper
Borel pair in the centralizer using the surviving root. The published solvable
maximal-torus conjugacy and proper fixed-point results produce its actual
proper Borel quotient. The existing rooted-solvable-quotient normalizer
construction then supplies a point whose relative Weyl-group class is
nonidentity.

`exists_normalizer_inverting_and_fixing` applies the published rank-one Weyl
action theorem to this point. The inverse normalizing automorphism negates
the specified root; composing with the direct automorphism proves the direct
inversion equation. Centrality of the defining cocharacter and
`normalizingAut_comp_of_central` give fixedness of that same cocharacter.
There is no replacement of it by another annihilating cocharacter.

In the original geometric fibre, the torus factors through the actual
geometric identity component. Self-centralization gives maximality there,
and locus membership gives its connected reductivity. The preceding
normalizer construction therefore applies. Its actual torus automorphism
gives the integral `normalizingCoordinateIso`. The character-lattice
equivalence identifies the specified character with its original exponent
vector, so the coordinate automorphism sends that vector to its negative.
The published `exponentCocharacter_rootCentralizerVector` comparison
identifies the defining cocharacter with the exact integer cocharacter
required by `GeometricRootReflectionData`. The normalizer point maps through
the actual centralizer inclusion to the original geometric identity
component; `IsTransporter.map` preserves its all-test transporter equation.
These data give the constructed record.

`RankOneCentralizerDetection.neg_mem_roots` applies the published
algebraically closed rank-one root-negation theorem inside this same
centralizer. The actual centralizer weight comparison sends the negative
root back to the original group. The geometric theorem
`splitTorus.neg_mem_geometricExponentRoots_intrinsic` transfers this fact
to the original exponent coordinates.

The provenance is internal composition of the existing generic cocharacter,
dynamic centralizer reductivity, actual root comparisons, proper Borel
quotient, rank-one Weyl action, central cocharacter fixedness, integral
coordinate recovery and transporter functoriality results. No universal
`RelativeRootReflectionExistenceStatement` is assumed or proved. In
particular, this construction does not assert that a normalizer centralizes
the full scheme-theoretic kernel of the root, and it does not construct
integral coroots or a complete root datum.

This is a field-input construction for the existing relative good-open
argument. It does not assert relative torus lifting, supply an initial
relative torus, or prove the universal openness proposition. There is no
restriction on characteristic, no Noetherian hypothesis and no
connectedness requirement on the original ambient fibres.
