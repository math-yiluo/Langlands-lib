# Socle and weight bounds of opposite-Borel induction: proof

`Langlands.GroupScheme.splitBorelInducedSocleAndWeights` proves the published
proposition `Langlands.GroupScheme.SplitBorelInducedSocleAndWeightsStatement.{u}`
(Milne, *Algebraic Groups*, 2022 corrected reprint, Proposition 22.27(b,c),
p. 471) for every universe `u`, with no hypotheses beyond those of the statement:
every field `k`, every split pinning `p` of an affine `G`, every proper
`HomogeneousQuotient` `D` of the opposite Borel inclusion and every torus
character `lam`. The module sets no options; its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

The route is built from the Library's theorems on covariant regular functions
and their finite socles, not transcribed from Milne's text.

## Setting

Write `V` for `inducedSpace p.negativeBorelHom (p.borelCharacter lam)` and `b`
for `inducedBasis p.negativeBorelHom D (p.borelCharacter lam)`. Then
`inducedRepresentation` unfolds to `affineRegularRepresentation G V b hV`, where
`hV`, stability of `V` under right translation, is
`AffineCoordinates.rightAct_mem_leftCovariantSubspace`. By definition `V` is the
left covariant subspace for `p.borelCharacterCoordinate lam`, which is the
hypothesis `hcov` of the two private lemmas below.

## Part (b): the unique simple stable subspace

Assume `p.IsDominantWeight lam`. The private lemma
`covariant_hasUniqueSimpleSubspace` does the work.

1. `p.isRealizedWeight_of_isDominantWeight'` gives a coordinate `f` with
   `p.IsRealizedBy lam f`, over an arbitrary field. Its finite regular socle
   `S = Chevalley.affineCovariantSocle G f` lies in `V` by
   `Chevalley.affineCovariantSocle_le_leftCovariantSubspace`.
2. In coordinates the inclusion `S ≤ V` is the matrix
   `C = coactionCoordinates V b (bS ·)`, for the finite basis `bS` of `S`.
   `Chevalley.intertwines_affine_coactionCoordinates` shows that `C` intertwines
   the socle representation with `ρ`, and
   `Chevalley.coactionCoordinates_mulVecLin_injective` shows that it is
   injective. The socle representation has highest weight `lam` by
   `SplitPinning.IsRealizedBy.isHighestWeight_affineCovariantSocleRepresentation`;
   in particular it is irreducible, so the image `W` of `C` is a simple stable
   subspace (`MatrixRepresentation.IsIrreducible.isSimpleStableSubspace_range`),
   and `C` itself is a `StableSubspaceRepresentation` of `ρ` on `W` whose
   representation is the socle representation, of highest weight `lam`.
3. Uniqueness. Let `T` be any simple stable subspace and `F` the injective map
   `Chevalley.affineRegularCoordinateMap G V b`
   (`Chevalley.affineRegularCoordinateMap_injective`). The image `T.map F` is
   nonzero, lies in `V`, and is stable under right translation by
   `Chevalley.rightAct_mem_map_affineRegularCoordinateMap`. The leastness theorem
   `Chevalley.affineCovariantSocle_le_of_nonzero_rightAct_mem`, applied with the
   positive unipotent subgroup and the big-cell coordinate
   (`SplitPinning.cellCoordinate_mem_nonZeroDivisors`,
   `SplitPinning.exists_factors_of_isUnit_cellCoordinate`), gives `S ≤ T.map F`.
   The private helper `coordinateInclusionCommutes` shows that `F ∘ C` is the
   coordinate map of `S`, so `W ≤ T`. Since `W ≠ ⊥` and `T` is simple, `T = W`.

## Part (c): the two weight bounds

Let `mu` be any occurring weight of the whole representation `ρ`; no dominance
is assumed. The private lemma `covariant_weight_bounds` proves both bounds.

1. The upper bound `lam - mu ∈ p.positiveRootMonoid` is
   `SplitPinning.affineRegularRepresentation_weight_le`.
2. The private lemma `weylWeightFinrank` shows that the dimension of a weight
   space is invariant under the Weyl group, by induction on the generating
   reflections (`RootPairing.weylGroup.induction`) from
   `SplitPinning.finrank_representationWeightSpace_root_reflection`. Hence
   `w⁻¹ • mu` is also an occurring weight, and the upper bound gives
   `lam - w⁻¹ • mu ∈ p.positiveRootMonoid`.
3. The private lemma `negWeylSendsPositive` takes `w` with the statement's
   hypothesis (a root index `i` is positive after applying `w` exactly when `i` is
   not positive) and shows that `x ↦ -(w • x)` maps `p.positiveRootMonoid` into
   itself. It suffices to treat the generators, the simple roots. A simple root
   `α` has height one, hence is positive, so its image `w • α` is a root that is
   not positive, hence negative
   (`RootPairing.Base.IsPos.neg_iff_not`), so `-(w • α)` is a positive root and
   lies in the monoid by `SplitPinning.root_mem_positiveRootMonoid`; the general
   case follows by `AddSubmonoid.closure_induction`. Applied to
   `lam - w⁻¹ • mu` it gives `mu - w • lam ∈ p.positiveRootMonoid`.

The target statement and the modules it imports are used unchanged.
