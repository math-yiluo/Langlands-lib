# Maximal pro-p conclusions from explicit structural inputs

This internal adapter concerns the actual point topology, zero subgroup, facets and
positive subgroups of a supplied `KPBuildingDatum D` over a nonarchimedean local field
in arbitrary universe `u`. The datum must satisfy its single-group axioms. The five
additional structural inputs are explicit: `FacetReductiveComparisons D`,
`FiniteFieldSylowBorelStatement.{u}`, `FiniteFieldNormalSylowTorusStatement.{u}`,
`LocalFieldPositiveProPStatement.{u}`, and
`RationalPoints.BoundedOpenNormalizerStatement.{u}`. The adapter proves none of these
inputs and does not supply an unconditional proof of the availability-only target.

`maximalProPConclusions_of_inputs` assembles precisely the existing
`MaximalProPConclusions D`. For every facet, the actual positive subgroup lies in the
zero subgroup by the model axioms, is open by the facet topology theorem, and is pro-p
by applying the explicit local-model input to its actual quotient. Chamber maximality
uses the containing-chamber construction, conjugacy and the unimodular Haar argument.
The converse and the normalizer identity use the explicit finite normal-Sylow and
bounded-normalizer inputs through the existing normalizer adapter. Domination and the
maximality clause classify every maximal open pro-p subgroup as a chamber positive
subgroup. For a chamber, the forward maximality result supplies the maximality premise
needed by the normalizer adapter. The normalizer is intersected with the actual zero
subgroup, exactly as in the corrected proposition.

The entry definition `chamberMaximalOpenProPEquiv` is an equivalence from the subtype
of actual chambers to the subtype of actual maximal open pro-p subgroups of the zero
subgroup. Its forward map sends a chamber to its existing `facetPositiveSubgroup`, with
the proved maximality certificate. Equal images have equal zero normalizers; the
normalizer identities and injectivity of facet zero fixers identify the chambers. This
proves injectivity. The preceding classification proves surjectivity. `Equiv.ofBijective`
then chooses the inverse of this precise forward map. No further equivalence of abstract
replacement groups is introduced.

`availableMaximalProP_of_inputs` promotes this single-datum construction to the existing
`AvailableMaximalProPStatement.{u}`, still conditional on five global proposition proofs.
Here the first input is `FacetReductiveComparisonStatement.{u}`. For each field, group
and assignment, availability supplies the single-group axioms. The comparison input is
applied to that same actual datum, and the assembled conclusions complete the implication.
It neither assumes full validity of the assignment nor adds a premise to the protected
target statement; instead, the extra assumptions are visibly retained on this intermediate
implication. Discharging them is still required before the host task can be completed.

The provenance is internal composition of the chamber maximality, maximal subgroup
classification, facet topology, actual local-model, positive-normalizer and fixer
injectivity constructions. The paired files of the target and its imports are unchanged.
