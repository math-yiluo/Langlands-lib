# Unequal-rank source assembly from the exact pending statements

This internal compatibility module defines the Prop-valued bundle
`UnequalRankAssembly.SourcePrerequisites`. It is exactly the conjunction,
in order, of the published
`Whittaker.MirabolicFiniteLengthStatement.{uF,uV}`,
`UnequalRankMirabolicPairingRigidityStatement.{uF,uV,uW} F T n r`,
and `UnequalRankCompactGenericPairingStatement.{uF,uW} F T n r`.
Defining this bundle establishes none of its three conjuncts.

The module proves
`UnequalRankAssembly.sourceLengthBound_of_statements` and then
`UnequalRankAssembly.unequalRankBilinearUniqueness_of_statements`.
Both retain those three explicit premises. The companion
`sourceLengthBound_of_prerequisites` and
`unequalRankBilinearUniqueness_of_prerequisites` unpack the named bundle
and apply the corresponding three-premise theorem. The module supplies a conditional
specialization of the published separate-group functional-factor assembly,
not an unconditional proof of either named conclusion.

The source-length conclusion is exactly the published
`UnequalRankSourceLengthBoundStatement.{uF,uV,uW} F T n r`.
Field and carrier universes remain independent, the supplied
`TopologicalData` is retained, and all natural ranks with `n < r` are
covered. Both published covariance laws, the determinant exponent
`(r-n)/2-s`, and the actual subgroup `U_(n+2,r+1)` are retained through the
published `UnequalRankMixedAdapter`.

## Irreducible-pair control

`pair_control_of_statements` takes smooth irreducible first factors on
the actual mirabolic group `P_(r+1)` and admissible irreducible second
factors on the original `GL_(n+1)`. It uses the exceptional set from the
rigidity premise unchanged, before the parameter and every form.

Nonzero mixed length equals nonzero length of the actual
`unequalRankMirabolicForms` by the published adapter. Length zero is
equivalent to the space being subsingleton, so nonzero length gives a
nonzero form. Applying rigidity gives an equivariant equivalence of the
first representation with `Whittaker.mirabolicCompactInduced` and an
inverse-standard nonzero functional on the second representation.
Irreducibility makes the first carrier nontrivial; evaluation on its
compact-model equivalence then gives its nonzero mirabolic functional by
`Whittaker.hasFunctional_of_mirabolicCompactEquiv`.

For the bound, zero mixed length is immediate. Otherwise the same
rigidity consequence identifies the first representation with the
compact model and supplies the second functional.
`MixedBilinear.length_congr_left` transports the full mixed form space
through that equivalence, without identifying the carrier universes.
The adapter identifies its length with the actual compact-model pairing
length. The compact/generic premise gives a linear equivalence of that
space with `ℂ`, whose length is one. Thus every controlled pair has
length at most one. This proof needs neither a multiplicity theorem nor
admissibility of the first irreducible.

## Original-carrier specialization

`sourceLengthBound_of_statements` uses the actual mirabolic restriction
of the first Whittaker-type representation and the unchanged second
general linear representation. The published specialization helpers
give smoothness and character local constancy, the first total
functional-space equivalence, finite length over each original general
linear group algebra, and compact-open cofinality for the second group.
The second total functional-space equivalence and its admissibility
come directly from its Whittaker-type hypothesis.

Only the first representation is restricted, using the exact mirabolic
finite-length premise and its original smoothness. The two unipotent
compact-limit theorems are applied independently over their respective
groups. The published
`MixedBilinear.exists_exception_length_le_one_of_admissibleSecond_finiteLength`
then uses the pair control above to construct a finite exceptional set
for the total representations. This set precedes the parameter and all
forms. The second group's admissibility remains explicit throughout;
it is never inferred from smooth irreducibility. Rewriting the total
mixed length by the public adapter gives the exact original-carrier
source-length statement.

Finally, `unequalRankBilinearUniqueness_of_statements` applies the
published `unequalRankBilinearUniqueness_of_source_length` to that
conditional source bound. The actual coefficient-model pullback and its
covariance transport are reused unchanged.

## Provenance and remaining obligations

This is internal derived algebra on the published mixed-filtration
bounds, functional-factor assembly, actual covariance adapter,
specialization inputs and coefficient-model descent. It follows the
existing conditional `EqualRankTrilinearPrerequisites` pattern but
retains independent ambient groups. No new original-literature
assertion is made. The three statement premises remain substantive
proof obligations; acceptance of this helper alone proves neither
their truth nor unconditional source length or full unequal-rank
uniqueness.
