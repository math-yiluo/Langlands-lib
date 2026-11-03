# Rank assembly from independent geometric comparisons

This derived unit constructs the actual linear decomposition associated with an independently established rational root/character complement and injectivity of rational character restriction. It is conditional and does not prove either geometric premise or the full `RelativeRankIdentityStatement`.

For the actual map `i : T.toGrp ⟶ G`, `relativeRootCharacterEquiv` maps a pair `(x, χ)` to `x + rationalCharacterRestrictRat i χ`. First `LinearEquiv.ofInjective` identifies the rationalized character module with the range of restriction. Mathlib's `Submodule.prodEquivOfIsCompl` then identifies the product of that range with the actual relative root span with the full rational character space of `T`. The accompanying formula specifies this map.

When `T` is split, its full rational character space is finite dimensional by `IsSplitTorus.finite_characterLatticeRat`. The finite-dimensional sum formula for complementary subspaces and the dimension of the range of an injective linear map prove `splitTorusRank T = relativeRootRank i + rationalCharacterRank G`. This uses the full torus character lattice and preserves rank zero and all actual relative roots.

The independent lemma `splitRank_eq_splitTorusRank_of_conjugacyStatement` uses the rank clause of the existing proposition `MaximalSplitTorusConjugacyStatement` as an explicit hypothesis. The coordinate comparison `splitTorusRank_eq_card_of_splitting` converts that clause to the intrinsic lattice rank. It proves no conjugacy or ambient rank equality without that hypothesis.

The provenance is internal and derived finite-dimensional linear algebra on published constructions. No new original-literature assertion is introduced. The exact unconditional rank theorem remains dependent on independently proved geometric comparisons.
