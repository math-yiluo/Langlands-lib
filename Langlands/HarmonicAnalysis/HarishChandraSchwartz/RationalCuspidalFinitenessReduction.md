# Structural choices for the conditional cuspidal finiteness reduction

This is a derived interface assembling existing Library results. Its entry
proposition, `RationalCuspidalFinitenessReductionStatement`, retains three
global premises: `BruhatTits.Iwasawa.IwasawaExistenceStatement`,
`RationalCuspidalCentralProjectionFiniteStatement`, and
`RationalCuspidalFixedCoefficientLiftingStatement`. It concludes the published
`RationalFixedCoefficientFinitenessStatement` with independent field and
representation-carrier universes `u` and `uV`. Neither unconditional finiteness
target is proved by this conditional interface.

The implemented structural adapter chooses a maximal split torus and generic
cocharacter using
`RationalPointFamily.exists_maximalSplitTorus_genericCocharacter` in
`Langlands.Representation.Aubert.General.StandardFamilyStructure`. The supplied
Iwasawa statement gives a special compact subgroup for this torus and chamber.
Its `SpecialCompactProperties` provide compactness and openness, and its
`ParabolicPointProductFamily` gives the minimal standard parabolic product.
`isIwasawaPair_of_pointProductEqualities` converts that product into exactly the
spherical-function factorization used by the cuspidal targets. No existence of
building data or of an Iwasawa subgroup is inferred from a conditional theorem.

The positive-dimensional closed matrix representation is provided by
`Langlands.Plancherel.exists_isClosedSubgroup_fin_succ` in
`Langlands.Representation.Plancherel.ParabolicCharacterDecayProof`.
The split-component inclusion is a closed immersion, so
`isClosedEmbedding_rationalPointMap` makes its rational-point image a closed
subgroup of the locally compact rational-point group. Its subgroup topology is
therefore locally compact. The adapter selects `Measure.haar` on this actual
image, with its induced Borel measurable space.

With those choices,
`RationalCuspidalCentralProjectionFiniteStatement.fixedCoefficientFiniteness`
applies to the arbitrary quotient Haar measure, compact open level, and
continuous unitary central character in the exact fixed-coefficient target.
That published theorem uses the actual level-preserving lifting premise and
the finite projected level span. The target's additional central-character
triviality assumption is not needed by this stronger conditional implication.
Finally,
`RationalFixedCoefficientFinitenessStatement.orbitFiniteness` supplies the
conditional discrete-series twist-orbit consequence.

The construction adds no analytic argument, reconstruction hypothesis, or
rank-induction step. The finite-projection and level-preserving lifting proofs,
as well as compact-open Iwasawa existence, remain obligations of their existing
owners. The provenance of this interface is the composition and structural
specialization of the named published declarations; it is not a new
translation of an original-source theorem.
