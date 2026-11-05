# Chamber splitting from the actual Iwahori–Weyl exact sequence

`IwahoriWeylChamberExactSequenceReductionStatement.{u}` is the implication from
the published global `IwahoriWeylExactSequenceStatement.{u}` to the unchanged
global `IwahoriWeylChamberSplittingStatement.{u}`.
`iwahoriWeylChamberExactSequenceReduction` proves this implication.
The exact sequence remains an explicit intermediate premise. This unit does
not prove either global target without that premise.

The new deduction removes the separate generic chamber-transport premise of
`IwahoriWeylChamberReductionStatement` and of
`iwahoriWeylChamberSplittingStatement_of_exactSequence` in
`IwahoriWeylExactSequenceReduction`. It supplies that premise with the proved
`affineChamberSimpleTransitivity`, imported by its Lean name.

For fixed actual data `P`, `existsUnique_affineWeyl_chamber_transport` applies
this generic theorem to `P.affineRoots` on `P.Apartment`. The AS3 field
`hP.isAffineRootSystem_affineRoots` supplies exactly the required
`IsAffineRootSystemWithRankZero` hypothesis. The conclusion uses the existing
reflection-generated affine Weyl group and its literal affine direct-image
action. It retains nonreduced systems and rank zero, and requires only two
given chambers; it makes no chamber-existence claim.

`ParahoricBuildingData.iwahoriWeylChamberSplitting_of_exactSequence` then feeds
this actual transport theorem into
`iwahoriWeylChamberSplitting_of_unique_chamber_transport`. That published
reduction extracts the two normalities, the action-compatible affine-part
isomorphism and component surjectivity from the supplied actual exact
sequence. Unique chamber transport gives freeness and transitivity for the
actual action; the reduction concludes normality of `P.affinePart`, its
complement relation with the full `P.chamberStabilizer C`, and bijectivity of
the restricted `P.toComponents` onto the full `G(F)/G(F)^0`.
The global implication applies this local deduction to each `F`, `G`, `P`
and chamber in the unchanged global target.

All statements retain the arbitrary field universe `u`, both local-field
characteristics, the actual normalizer action, and the original apartment
axioms. No new normality, action, component or chamber-group hypothesis is
hidden in the deduction. Proving the actual exact sequence remains the
separate algebraic obligation of the host task.

The provenance is internal assembly from the published generic chamber proof
and the published actual quotient and chamber-complement lemmas. Its
contextual source is KP 7.8.2 and the chamber consequence of KP Lemma 1.3.17,
as documented in the unchanged `IwahoriWeylStatement` and
`AffineChamberTransitivityStatement` pairs. The argument here is precisely the
specialization and composition described above.
