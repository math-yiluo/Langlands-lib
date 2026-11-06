# Conditional uniqueness of the supercuspidal correspondence

This is a derived supporting interface for the existing supercuspidal
correspondence specification. It proves a conditional uniqueness reduction.
It does not prove either of its substantive premises, correspondence existence,
or the closed `SupercuspidalCorrespondenceStatement`.

## Statement and scope

`SupercuspidalCorrespondenceUniquenessReductionStatement.{uF,uP,uA}` says
that the existing all-field supercuspidal local-converse proposition and the
existing same-family nonabelian-system uniqueness proposition together imply
`SupercuspidalCorrespondenceUniqueness` over every prime and every p-adic field.
The field, Weil-parameter carrier and automorphic-representation carrier
universes remain independent. Local converse is used at automorphic carrier
universes `uA,uA`, and nonabelian uniqueness at field and parameter universes
`uF,uP`.

`supercuspidalCorrespondenceUniquenessReduction` proves this conditional
proposition. The fieldwise theorem
`supercuspidalCorrespondenceUniqueness_of_nonabelianUniqueness` only requires
same-family assignment uniqueness for the chosen field, in addition to the
displayed all-field local-converse input. The final fieldwise corollary replaces
assignment uniqueness with the actual
`CommonClosureDegreeZeroGeneration` premise, using its published reduction.
Generation remains a premise of that corollary.

## Implemented argument

The helper
`commonSupercuspidalEpsilonFactors_of_arithmeticComparison` extracts arithmetic
epsilon certificates for the same Weil pair from two separate pair-factor
compatibility witnesses. It transports the first certificate to the second
system using `ArithmeticPairEpsilonComparison`, then uses fixed-system
coefficient and exponent uniqueness to obtain one common JPSS epsilon
certificate. This supplies the exact relation consumed by the published
supercuspidal rank induction.

For two maps satisfying `IsSupercuspidalCorrespondence`, the fieldwise proof
extracts their independently supplied reciprocity candidates, common-closure
families, assignments and compatibility witnesses. The published theorem
`LocalClassField.commonClosureReciprocityUniqueness` identifies the normalized
families. Base-component coherence identifies the standalone candidates.
The published rank-one comparison then identifies the rank-one maps.
The retained same-family assignment-uniqueness premise supplies the arithmetic
epsilon comparison.

The published
`HarmonicAnalysis.padicUnitaryAdditiveCharacterExists` supplies an actual
nontrivial unitary additive character for the canonical topology. The first
correspondence premise supplies a self-dual Haar measure through
`IsSupercuspidalCorrespondence.exists_selfDualMeasure`; no separate measure
existence assertion is assumed. Rankwise bijectivity of that same map supplies
surjectivity at every test rank. The published
`supercuspidalMap_eq_of_commonEpsilonFactors` applies local converse and strong
rank induction to conclude equality of the two actual map families.

The proof uses the rank-one, bijectivity and epsilon components of the stronger
correspondence predicates. Their remaining compatibility clauses need no
additional construction for this uniqueness implication.

## Provenance and remaining obligations

The conceptual rank-induction route is Henniart, *Une preuve simple des
conjectures de Langlands pour GL(n) sur un corps p-adique*, Inventiones
Mathematicae 139 (2000), section 1.4, printed page 441, retained PDF page 3
(registered source `henniart-2000-simple-proof`). The present module is an
internal composition of the published actual-class and arithmetic-system APIs;
the named conditional proposition and the extraction of witnesses are project
formulations, rather than a claimed verbatim theorem from that article.

The two remaining inputs are precisely
`RankinSelberg.SupercuspidalLocalConverseStatement.{uF,uA,uA}` and
`LocalFactor.NonabelianSystemUniquenessStatement.{uF,uP}`. Their proof tasks,
and the separate actual common-closure generation proof task, remain independent
mathematical obligations. No numerical surjectivity theorem or global
automorphic construction is used here: surjectivity is extracted from an
already supplied correspondence premise. In particular, the result gives no
existence of such a correspondence.
