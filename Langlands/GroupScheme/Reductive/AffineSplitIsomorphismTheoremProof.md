# Isomorphism Theorem over an affine base

`Langlands.GroupScheme.affineSplitIsomorphismTheorem` proves exactly
`AffineSplitIsomorphismTheoremStatement.{u}` in every universe, with no added
hypotheses. It applies over every commutative ring to the reductive groups,
closed fibrewise-maximal coordinate split tori, root data and free rank-one
root spaces specified by that published statement.

First, `localSplitWeylConjugation_of_partner` applied to
`localSplitRootPartnerUniqueness` and `localSplitRootPairRescaling` supplies the
local Weyl-conjugation statement. The proof then applies
`affineSplitIsomorphismTheorem_of_weylRelations` and supplies its four inputs by
the following imported results:

1. `AffineSplitWeylNormalization.exists_simpleRootFamily_of_free` constructs the
   Weyl-normalized simple-root and opposite-root families from the target's
   free rank-one root spaces over any commutative ring.
2. `localSplitWeylCommutator_of_weylConjugation` supplies the local commutator
   statement from `localSplitRankOneNormal` and the derived local
   Weyl-conjugation statement.
3. `localSplitWeylNegSimple_of_rankOne` supplies the negative-simple relation
   statement from the same normalization and conjugation results and
   `localSplitRankOneBruhat`.
4. `LocalSplitCell.nonempty_exponentWeightSpace_precompTorus` transports
   root-space freeness to the common coordinate torus.

The imported affine assembly transports the local relations to each local test
ring over the original affine base and glues the coordinate cell maps. It
constructs an isomorphism preserving the supplied torus embeddings through the
torus isomorphism of the given root-datum equivalence. Evaluating its actual
exponent-character identity on every test scheme gives the precise monomial
pullback identity in the target.

This is an internal composite proof. It changes neither the target declaration
nor its imports.
