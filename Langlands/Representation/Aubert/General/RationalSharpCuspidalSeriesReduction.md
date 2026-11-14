# Cuspidal-series retention by `E#` from support retention and irreducibility

Authors:

* Workers 1166 and 4221: the transport helper and the conditional assembly.
  They are in the shared draft of Task 4221
  (`6316db5a-5618-43bb-a920-eadd3a912b88`), revision 2.
* Worker 29, with coauthor Worker 3640 (Task 3640): the final theorem
  `rationalSharpCuspidalSeriesReduction`. Worker 29 also rechecked the module
  against Library `3489c50380b46cfbdad8997457a217e6e8e6a27d`, which
  contains the published statement module
  [`RationalSharpReductionStatements`](RationalSharpReductionStatements.md).
* Worker 443 (Task 6484, `b5652c2b-8c8a-41a5-9af8-09a7f7a8412c`): rechecked
  the unchanged Lean module against Library
  `c40a01345b2f4172fa41e07ff31644b40e695003` and submitted it.

This module reduces the exact rational target
`RationalSharpCuspidalSeriesStatement` of
[`RationalSharpConsequenceTargets`](RationalSharpConsequenceTargets.md) to two
sibling targets in the same module: `RationalSharpSupportRetentionStatement`
and `RationalSharpIrreducibleStatement`. The main theorem is conditional. It
takes both sibling statements as hypotheses, so it proves the cuspidal-series
target only after both are proved. Nothing in this module proves either sibling
statement.

The content is derived and internal. The generic target's Markdown
([`SharpConsequenceStatements`](SharpConsequenceStatements.md)) describes the
route used here. Aubert uses retention of the cuspidal series in the proof of
Corollaire 3.9 (c) (Trans. AMS 347 (1995), p. 2189). It follows from three
facts: support retention on the full smooth support category `Alg({I})`
(erratum, Trans. AMS 348 (1996), p. 4687), Corollaire 3.9 (b), and the
definition of `Alg({I})`. The deduction also needs conjugation by an
association representative to preserve irreducibility and inside-Levi
cuspidality. This module only assembles the deduction. It adds no root-system,
Coxeter, endpoint, finite-length, admissibility or compactness premise.

## Generic transport helper

`Langlands.Aubert.General.associationCuspidalTransport_of_isLeviCuspidal`
works for arbitrary families `P M U`, closedness data `hclosed hM`, inside-Levi
decompositions `hL`, an arbitrary association predicate `IsAssociate` and an
arbitrary carrier universe `uW`. It assumes `hconj`: whenever
`IsAssociate I J n` holds and `n` satisfies the membership condition
`x ∈ M J ↔ n⁻¹ x n ∈ M I`, the conjugate `(conjugationFunctor n hn).obj σ` of
an inside-Levi cuspidal `σ` of `M I` is inside-Levi cuspidal on `M J`. It
concludes the published `AssociationCuspidalTransport` (from
[`SharpCuspidalSeriesReduction`](SharpCuspidalSeriesReduction.md)), which also
asks for irreducibility of the conjugate. That part holds because the
conjugate's representation is `σ.representation` composed with the
topological group isomorphism `conjugationEquiv n hn`. Then
`isIrreducible_comp_continuousMulEquiv_iff` transfers irreducibility.

The helper is stated generically on purpose. With the same anonymous
constructor elaborated directly in the rational context, the kernel check hit a
deterministic timeout.

## Rational assembly

`Langlands.Aubert.General.RationalPointFamily.rationalSharpCuspidalSeries_of_supportRetention_of_irreducible`
assumes `RationalSharpSupportRetentionStatement.{u, v}` and
`RationalSharpIrreducibleStatement.{u, v}`. It proves
`RationalSharpCuspidalSeriesStatement.{u, v}`. After introducing the target's
binders, it installs the same local instances as the target statements: the
affineness and monomorphism instances, `pointTopology` and
`simpleRelativeRootFintype`. Then it applies the published generic reduction
`sharpCuspidalSeries_of_irreducible_supportRetention` (from
[`SharpCuspidalSeriesReduction`](SharpCuspidalSeriesReduction.md)) to the
literal families `parabolic i ν`, `levi i ν`, `unipotent i ν` and the actual
`rootAssociation i ν hN hZ`, with these four inputs:

* `hirr` is the irreducibility statement applied to the target's binders. That
  statement takes no `hN` or `hZ` argument.
* `hret` is the support-retention statement applied to the same binders,
  including `hN` and `hZ`.
* `hrefl : AssociationReflexive (rootAssociation i ν hN hZ)` is
  `rootAssociation_one` (from [`RootAssociationLaws`](RootAssociationLaws.md)).
  It says the literal identity point associates every root subset to itself.
* `htrans` is the generic helper above, applied to the published
  `isLeviCuspidal_conjugation` (from
  [`RationalSupportAssociationInvariance`](RationalSupportAssociationInvariance.md)).
  That theorem takes the target's `hG`, `hi`, `hν`, `hStandard`, `hInter`,
  `hRoots`, `hN`, `hZ`, `hU` and `hM`. Its inside-Levi decompositions are
  `isSemidirectDecomposition_in_levi i ν hInter hG hi hν`, the same terms the
  target statement uses.

The carrier universe of the transport is
`max u (max u (max (u + 1) v)) = max (u + 1) v`, the target's carrier universe.
`isLeviCuspidal_conjugation` is universe-polymorphic in its carrier, so it
applies there.

The published generic reduction then does the rest. For `E ∈ 𝔈(I)` it puts
`E` in `Alg({I})` by `IsInCuspidalSeries.isInSupportCategory` and `hrefl I`, and
it gets irreducibility of `E#` from `hirr`. Next it applies `hret` and the
definition of `Alg({I})` to `E#`, which is an irreducible subquotient of itself
(`SmoothRep.isSubquotient_self`). This gives `J`, `n`, the membership condition,
`rootAssociation I J n` and an irreducible inside-Levi cuspidal `σ` of `M I`
with `E#` a subquotient of the normalized induction from `M J` of the
conjugate of `σ`. `htrans` makes that conjugate irreducible and inside-Levi
cuspidal on `M J`, so `E# ∈ 𝔈(J)`.

Every premise and quantifier of the target is kept, and both universes stay
independent.

## The published reduction proposition

`Langlands.Aubert.General.RationalPointFamily.rationalSharpCuspidalSeriesReduction : RationalSharpCuspidalSeriesReductionStatement.{u, v}`
proves the published proposition of
[`RationalSharpReductionStatements`](RationalSharpReductionStatements.md).

* That proposition is the curried implication
  `RationalSharpSupportRetentionStatement → RationalSharpIrreducibleStatement → RationalSharpCuspidalSeriesStatement`,
  at universes `{u, v}`.
* The proof takes the two hypotheses `hSupp hIrr` and returns
  `rationalSharpCuspidalSeries_of_supportRetention_of_irreducible hSupp hIrr`.
* The binders and universes of the inputs and of the conclusion are those of
  the published propositions. The theorem adds no other premise.

Library `c40a0134…` proves neither input; it contains only the conditional
reductions below.

* `RationalSharpSupportRetentionStatement`: owner task
  `d441ca88-a2fa-4174-93e0-97d1b9fca9ba`. The published conditional theorem
  `rationalSharpSupportRetention_of_inductionJacquet`
  (`SharpSupportRetentionReduction`) derives it from
  `RationalSupportCategoryInductionJacquetStatement`.
* `RationalSharpIrreducibleStatement`: owner task
  `44d0ed8c-18a6-44f8-8836-dc351694e9d9`. The published theorem
  `rationalSharpIrreducibleReduction` (`SharpIrreducibleReduction`) derives it
  from the dynamic finite-length statements, induction compatibility,
  involutivity and the class formula `RationalSharpClassFormulaStatement`.

This module neither imports nor uses those two reductions.

## Dependencies

The final theorem `rationalSharpCuspidalSeriesReduction` only applies
`rationalSharpCuspidalSeries_of_supportRetention_of_irreducible`.

Declarations used directly: `sharpCuspidalSeries_of_irreducible_supportRetention`,
`AssociationCuspidalTransport` and `AssociationReflexive`
(SharpCuspidalSeriesReduction), `isIrreducible_comp_continuousMulEquiv_iff`
(CompactCoefficient.GroupTransport), `conjugationFunctor` and
`conjugationEquiv` (Parabolic), `rootAssociation_one` (RootAssociationLaws) and
`isLeviCuspidal_conjugation` (RationalSupportAssociationInvariance). The
published reduction itself uses `IsInCuspidalSeries.isInSupportCategory`
(SupportCategory) and `SmoothRep.isSubquotient_self`
(SharpCuspidalSeriesReduction).

This module uses no Langlands classification, character independence,
geometric lemma or adjunction result. The declarations it calls are formal
transport results: of irreducibility along a topological group isomorphism, of
inside-Levi Jacquet vanishing along conjugation by an association
representative, and of the identity association. Any use of such results in
the proofs of the two sibling statements belongs to those proofs. The final
proof records it when it imports them.
