# Conditional assembly of induced localization

Author: Worker 330.

This internal construction assembles the actual upper block-induction character
quotient equivalence from four explicit closed propositions. It does not prove
those propositions and does not prove the closed
`Langlands.InducedLocalizationStatement`. It adds no external literature claim;
its provenance is the composition of the published APIs named below with the
four inputs.

`Whittaker.inducedLocalization_of_prerequisites` has precisely these inputs:

- `UnipotentOrbitStatement.{uF}`;
- `NonOpenCharacterWitnessStatement.{uF}`;
- `CompactLocalizationStatement.{uF, uV}`;
- `Jacquet.Localization.FiltrationCollapseStatement.{uF, max uF uV}`.

Its conclusion is `InducedLocalizationStatement.{uF, uV}`. The independently
universed field and coefficient carriers, arbitrary admissible finite-type block
representations, original ordered blocks, upper unnormalized smooth induction,
and positive raw character quotient are those of that published conclusion.
Admissibility is used through smoothness of each block; finite generation is
retained as a hypothesis but is unused by this assembly.

`Whittaker.inducedLocalizationEquivOfPrerequisites` takes the same four inputs
and all the data and hypotheses of that conclusion, and chooses the resulting
complex linear equivalence with `Classical.choice`. This is a choice of an
actual equivalence between the existing relation-span quotients. No formula,
canonicity, integral realization, or independence of that choice is asserted.

The proof first equips the canonical p-adic field, general linear group, and
upper-unipotent group with their published topology and compactness instances.
`ContinuousCharacterProof` and the identity between the raw and standard
characters give an open kernel. The elementary open-kernel argument gives local
constancy. `upperUnipotent_isLimitOfCompactSubgroups` supplies the compact-limit
hypothesis for the full acting subgroup, and `parabolicQuotientCompact` supplies
the compact parabolic quotient.

The orbit proposition supplies an actual ordered orbit filtration with its
permutation representatives. Its index for the inverse block-reversal
permutation is selected through the supplied finite equivalence; it need not
be an endpoint. `closedSubgroupMackeyFiltration` identifies each actual graded
representation with compact induction from the corresponding orbit stabilizer.
The compact-localization input and `Localization.representationEquiv` identify
their character quotients.

For every other index, the witness input supplies an element with identity Levi
projection and nontrivial ambient character. That element acts trivially on the
Levi-inflated coefficient module, so
`Localization.subsingleton_of_trivial_action` annihilates its quotient. The
filtration-collapse input then identifies the ambient quotient with the chosen
quotient. Its carrier universe is `max uF uV`, since induced functions depend
on both field and coefficient carriers.

For the surviving representative, the published
`openStabilizerLocalizationEquiv` identifies the stabilizer quotient with the
tensor of the block character quotients in their original order and with the
unchanged character. A local lemma parametrized by the representative handles
its equality to inverse block reversal together with every dependent quotient
module instance. Finally, `rawRestrictedCompactSmoothIso`,
`Representation.equivOfIso`, and the localization restriction equivalence
identify the restricted compact-induction quotient with the upper smooth
parabolic-induction quotient. Composing these full equivalences proves the
conditional conclusion.

The four prerequisite proofs, the closed theorem `Langlands.inducedLocalization`,
its exact-target proof validation, and its independent acceptance and publication
remain separate obligations of the parent task. Acceptance of this conditional
constructor discharges none of them.
