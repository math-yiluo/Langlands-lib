# Haboush's theorem through the rank-one central cover

## Statement

`Langlands.GroupScheme.IndependentHaboush.reductiveGeometricReductivity` proves the published
proposition `Langlands.GroupScheme.ReductiveGeometricReductivityStatement.{u}` for
every universe `u`. It adds no hypothesis. The proposition is Haboush's theorem (Mumford–Fogarty–
Kirwan, *Geometric Invariant Theory*, Appendix to Chapter 1, Theorem A.1.0, a) ⇒ b)). Let `k` be an
algebraically closed field of any characteristic and `G` a pseudo-reductive (over `k`: connected
reductive) group scheme over `Spec k`. Let `ρ : G ⟶ GL_n` be a representation on a finite
coordinate type `n`, and let `v ≠ 0` be a fixed vector. Then some homogeneous polynomial `F` of
positive degree is `G`-invariant over every test scheme and satisfies `F(v) ≠ 0`.

The module also proves two intermediate implications:

- `IndependentHaboush.splitRootLieLine_of_centralCover`:
  `RankOneCentralCoverStatement.{u} → SplitRootLieLineStatement.{u}`;
- `IndependentHaboush.reductiveGeometricReductivity_of_centralCover`:
  `RankOneCentralCoverStatement.{u} → ReductiveGeometricReductivityStatement.{u}`.

The final theorem applies the second implication to `rankOneCentralCover`, the published proof of
`RankOneCentralCoverStatement` (module `Reductive/RankOneCentralCoverProof`). That proposition says the following. Let `G` be a
connected reductive group over an algebraically closed field, with a split maximal torus `T`.
Suppose `G` has a root and its roots are pairwise linearly dependent. Then there are a split
torus `C`, a central isogeny `f : SL₂ × C ⟶ G` and an isogeny `t : D × C ⟶ T`, where the
one-dimensional split torus `D` maps to `SL₂` as the diagonal torus `z ↦ diag(z, z⁻¹)`. On
`D × C` the map `f` equals `t` followed by the inclusion of `T`.

## Proof

All steps take place at the same universe `u`. Each step is a published Library theorem, except
the theorems of this module and of its two helper modules `IndependentHaboushReduction` and
`SimplyConnected/SplitCoverOfRootDatum`, which were ported together with this module.

1. **Root datum.** `rankOneRootReducedness_of_centralCover`
   (`Reductive/RankOneRootReducednessFromCentralCover`) turns the cover into
   rank-one root reducedness over every field. `rootDatumExistence_of_rankOneReducedness`
   then gives `RootDatumExistenceStatement.{u}`.
2. **Root cells.** `splitRankOneRootCell_of_centralCover`
   (`Reductive/IndependentRootCellReduction`) gives
   `SplitRankOneRootCellStatement.{u}`.
3. **Root lines** (`splitRootLieLine_of_centralCover`, this module).
   `splitRootLieLine_of_rankOne` (`Reductive/RootLieLineRankOneReduction`) takes the published
   `dynamicCentralizerReductive` and reduces the statement to groups whose roots are pairwise
   dependent. For such a group, the root datum `P` of step 1 has root set equal to the set of
   roots, so a root `χ` is `P.root r` for some index `r`. The support-line statement
   `splitRankOneRootSupportLines_of_algClosed (algClosedRankOneRootSupportLines_of_centralCover
   hcover)` then gives a `k`-linear isomorphism from `k` to the weight space of `χ` (its second
   component).
4. **Coroot span.** `splitSimplyConnectedCorootSpan_of_corootSpanLineInputs`
   (`SimplyConnected/SplitCorootSpanLineReduction`) proves the coroot-span statement from the root datum, the root cells and the root lines.
5. **Opposite factor pairs.** `algClosedOppositeFactorPairs_of_structuralStatements` uses the
   same three inputs.
6. **Steinberg big cell.** The five inputs form an `IndependentSteinbergInputs` record.
   `IndependentSteinbergInputs.to_statement` turns it into `SteinbergBigCellStatement.{u}`.
7. **Assembly.** `IndependentHaboush.reductiveGeometricReductivity_of_rootDatum_and_bigCell`
   (helper module `IndependentHaboushReduction`) proves the target from the root datum and the
   big cell. Root-datum existence gives split simply connected covers
   (`splitSimplyConnectedCoverExistence_of_rootDatumExistence`, helper module
   `SimplyConnected/SplitCoverOfRootDatum`). In positive characteristic the separator comes from
   the central–derived product and the Steinberg big cell of the simply connected cover. In
   characteristic zero it comes from complete reducibility of the Lie algebra.

## Independence from the excluded inputs

The excluded inputs are `ParabolicDynamicStatement`, `RegularCocharacterBorelStatement`,
`RankOneSolvableObstructionStatement`, `RankOneBorelDynamicStatement` and
`RankOnePositiveRootUniquenessStatement`, their proofs (`parabolicDynamic`,
`regularCocharacterBorel`, `rankOneSolvableObstruction`, `rankOneBorelDynamic`,
`rankOnePositiveRootUniqueness`), the regular-cocharacter/Borel route, results proved from
these, and the Library's other proof `reductiveGeometricReductivity` (module
`Reductive/GeometricReductivityProof`).

The dependency check computed the type-and-value closure of
`IndependentHaboush.reductiveGeometricReductivity` in the Lean environment of this module.
Starting from the theorem, it follows every constant in the type and the value of each reached
constant, including theorem proof terms, instances and auxiliary `_proof` constants. The closure
has 128,775 constants, 29,761 of them in the `Langlands` namespace. It contains none of the ten
excluded constants. It also contains none of the following:

- the Library proofs on the excluded route: `reductiveGeometricReductivity`, `rootReducedness`,
  `rootDatumExistence`, `steinbergBigCell`, `absoluteBruhatCovering`, `splitRankOneRootCell` and
  `splitRootLieLine` (the last through the projective-Borel tangent chain below);
- the regular-cocharacter Borel steps: `IsRootDatumOf.isBorelPair_polarization_rho`,
  `IsRootDatumOf.bruhatCovering_polarization_rho`,
  `SplitPinning.canonicalRhoBorelBigCellGeometricData`;
- the properness of parabolic quotients and the linear-quotient-affine and dynamic-quotient
  statements: `parabolicSubgroupQuotientProper`, `ReductiveLinearQuotientAffineStatement`,
  `DynamicQuotientProperStatement`;
- the projective-Borel root-tangent chain, which the root-line proof
  `splitRootLieLine_of_rankOne` avoids:
  `rankOne_rootTangent_le_one_of_projectiveBorelInputs`, `prescribedBorelProjectiveCurveData`,
  `rootLieLine_of_dynamicCentralizerReductive`, `weightKernelTrivial_of_orthogonal`,
  `splitCommonTorusLeviGluing`.

As positive controls, the same check finds excluded constants in the closures of the Library
proofs `reductiveGeometricReductivity`, `rootReducedness`, `rootDatumExistence`,
`steinbergBigCell`, `absoluteBruhatCovering` and `splitRankOneRootCell`.

`rankOneCentralCover` does not assume its own statement: no constant in its closure has
`RankOneCentralCoverStatement` among its hypotheses.

The closure reaches four general Library curve lemmas, all through
`RankOneFlag.CoreData.finrank_tangent_le_one` in the proof of `rankOneCentralCover`:
`HomogeneousQuotient.curveUnipotentDataOfPseudoReductive`,
`HomogeneousQuotient.unipotent_dimension_le_one`,
`SchemeAction.unipotent_dimension_le_one_of_dominant_orbit` and
`SchemeAction.range_eq_bot_of_unipotent_kernel`. They are applied to the ordinary flag variety
`G/B`, with `dim G/B ≤ 1` obtained from Białynicki-Birula limits, the fixed points and
Hartogs/purity. This use does not make the proof depend on the excluded inputs: the lemmas
lie upstream of the excluded route and their hypotheses name no excluded statement.
The consumers of these lemmas on the excluded route are not reached:
`positive_roots_eq_of_rankOne_curve_quotient`, `signedCurveUnipotentDataOfPseudoReductive` and
`prescribedBorelProjectiveCurveData`. The Markdown of `RankOneCentralCoverProof` records the
same check for the cover proof.

The closure also shares general Library modules with the closures of the excluded proofs: scheme
theory, group schemes, ordinary Borel and flag geometry, and tangent spaces. None of these shared
constants has an excluded constant in its own closure. Ordinary Borel geometry whose closures
are clean is allowed, and shared upstream lemmas of this kind do not count as dependence.

The check ran on the sources over Library commit `f050c0b1` (18 November 2026). It uses the
method of the note `notes/group-schemes/haboush-independence-audit.md` (Method section), with
the watch lists above. The closure can be recomputed in this module's environment.

## Provenance

This is an internal composition of published Library results:
the cover (`rankOneCentralCover`), reducedness from the cover
(`rankOneRootReducedness_of_centralCover`), root cells from the cover
(`splitRankOneRootCell_of_centralCover`), root lines from rank one (`splitRootLieLine_of_rankOne`),
coroot span from root lines (`splitSimplyConnectedCorootSpan_of_corootSpanLineInputs`), the
Steinberg inputs (`IndependentSteinbergInputs`, `Reductive/SteinbergBigCellIndependentInputs`) and
the opposite-factor-pair reduction
`algClosedOppositeFactorPairs_of_structuralStatements`. The mathematical route follows the classical structure
theory. A rank-one group is a central quotient of `SL₂ × C`, and this gives the root datum, the
root groups and the big cell. Haboush's proof of geometric reductivity then uses the Steinberg
module of the simply connected cover (Mumford–Fogarty–Kirwan, Appendix to Chapter 1, Section A).
The Lean route does not prove these classical facts again: they are the published Library steps
named above.
