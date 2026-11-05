# Parahorics without relative roots

This derived unit handles the case with no relative roots in the
chamber-conjugate intersection problem. It uses the current definitions of
the actual sharp fixer and full parahoric, without any algebraic factorization,
ordered-product or centralizer-comparison premise. Worker 1674 is the author.

## Scope and constructions

For an arbitrary field and an existing `D : KPApartmentData i ω`,
`sharpFixer_eq_bot_of_relativeRoots_eq_empty` proves that `D.sharpFixer Ω`
is trivial whenever `relativeRoots i = ∅`. The subset `Ω` is arbitrary,
including the empty subset. The definition of the sharp fixer is a supremum
indexed by relative roots; the proof supplies an empty-index instance and
evaluates that supremum.

For actual `P : ParahoricBuildingData G` over any nonarchimedean local field
at arbitrary universe `u`,
`parahoric_eq_centralizerZeroImage_of_relativeRoots_eq_empty` then identifies
every `P.parahoric Ω` with
`P.centralizerZero.map (rationalPoints.map P.centralizer.j)`. It evaluates
the defining join with the trivial sharp fixer.

The entry
`parahoricEquivCentralizerZeroImage_of_relativeRoots_eq_empty` is the
multiplicative equivalence induced by that subgroup equality. It preserves
the ambient rational point, as stated by its application lemma.

The theorem
`iInf_parahoric_normalizerZeroComponent_eq_of_relativeRoots_eq_empty`
proves the corresponding intersection equality for all
`n : P.normalizerZeroComponent`, with the existing action of the actual
normalizer on any subset `C`. Each term of the infimum is the same
centralizer-zero image, so the infimum is constant. The index is nonempty
because it is a subgroup.

The membership theorem
`mem_centralizerZero_of_forall_mem_parahoric_of_relativeRoots_eq_empty`
has the original normalizer and zero-subgroup quantifiers of the
chamber-conjugate intersection target. Its proof specializes the
intersection hypothesis to the identity normalizer and rewrites the
root-free parahoric. Neither a chamber condition nor the apartment axioms
are needed for this case.

Finally, `parahoric_eq_centralizerZeroImage_of_isAnisotropic` applies the
published fact that a split subtorus of an anisotropic group has no relative
roots. The supplied maximal split torus provides that split subtorus.

## Provenance and remaining target

This is internal derived content from `KPApartmentData.sharpFixer` in
`KPBuilding`, `ParahoricBuildingData.parahoric` in `KPParahoric`, and
`IsAnisotropic.relativeRoots_eq_empty` in `Rational.RelativeRoots`.
It introduces no new assertion from external literature and changes none
of those definitions.

The hypothesis `relativeRoots P.i = ∅` restricts this unit to the case
without relative roots. It does not prove
`ChamberConjugateIntersectionStatement` for arbitrary supplied data and
does not discharge the remaining factorization, root-product or
centralizer-comparison obligations in that general case.
