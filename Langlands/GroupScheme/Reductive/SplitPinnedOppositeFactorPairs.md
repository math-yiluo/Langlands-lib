# Actual opposite factor pairs for split pinned groups

This internal proof establishes `splitPinnedOppositeFactorPairs`, the
published `SplitPinnedOppositeFactorPairsStatement`, over every field and at
arbitrary universe. More generally, `hasOppositeFactorPairs_of_rootDatum`
works for a connected reductive group with a supplied split maximal torus and
an actual root datum. It uses no perfectness, characteristic, or isogeny-type
assumption.

The rank-one step, `exists_oppositeFactorPair_of_rankOne`, takes the actual
root-cell parametrizations supplied by `rankOne_exists_rootCell`. Its imported
geometric inputs are the proved `dynamicCentralizerReductive`,
`rankOnePositiveRootUniqueness`, and `splitRootLieLine`. The root datum supplies
a normalizing point inducing the lattice reflection; the represented coroot
centralizer forces its square to lie in the torus. Smooth connected groups
are irreducible here by the imported `DynamicConnected` theorem. These facts
supply `RankOneRootCellRelation.WeylData`.

The actual positive root subgroup lies in the positive coroot dynamic
unipotent because the root-coroot pairing is two. Representability by the
positive additive parametrization therefore lifts the given rational root
point to the affine line. Nonidentity excludes coordinate zero, so that
coordinate is a unit over the base field. The generic
`WeylData.exists_oppositeFactorPair` from `RankOneRootCellFactorPairs` now
produces the required pair.

For an arbitrary indexed root, the proof chooses a cocharacter orthogonal to
that root and generic with respect to the other roots, by
`RootReducedness.exists_cocharacter_pairing_eq_zero`. Its dynamic centralizer
is represented by the closed subgroup `Dynamic.Affine.centralizerHom` and is
connected reductive by `dynamicCentralizerReductive`. The original torus
factors through it and remains maximal. `dynamicCentralizerRoots` identifies
its roots as the ambient roots orthogonal to the chosen cocharacter. Genericity
makes all such roots pairwise dependent. The restricted root datum is
`Langlands.LinearAlgebra.orthogonalRootPairing`, and
`IsRootDatumOf.orthogonalRootPairing` proves that it is an actual root datum
of this same torus in the centralizer.

The all-test equality `LeviGluing.root_map_centralizer` lifts the original root
point into the intrinsic centralizer root subgroup. Its lift is nonidentity,
since group homomorphisms preserve identity. Apply the rank-one step there and
map its ordered pair back to the ambient group using
`RelativeRoot.IsOppositeFactorPair.map`. This proves all the actual
opposite-factor-pair conditions, including normalization of the supplied
torus. Specializing to the fields of a `SplitPinning` gives
`splitPinnedOppositeFactorPairs`.

All inputs are imported by their Lean names. This unit is an internal
derivation combining the published root-cell, cocharacter-centralizer,
orthogonal-root-datum, and actual root-subgroup transport results. It does not
claim a new translation of an original-literature assertion. The cocharacter
centralizer is used to construct pairs and map them to the ambient group;
no identification with a full character-kernel centralizer is needed.
