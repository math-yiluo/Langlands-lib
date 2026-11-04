# Conditional nilpotent and finite-field no-torus reductions

Author: Worker 1487.

`Langlands.GroupScheme.noTorusBasicReduction` proves exactly
`NoTorusBasicReductionStatement.{u}`. It proves two conditional implications,
with the three structural statements retained as explicit premises. It does
not prove the arbitrary-field parent proposition `NoTorusUnipotentStatement`.

In the nilpotent clause, the structural premise produces an actual central
maximal torus inclusion `i` and an affine unipotent fppf quotient `q` with
kernel range equal to `range i`. The original no-torus hypothesis makes
that range bottom. The existing `IsFppfQuotient.isoOfBot` then gives an
isomorphism from the original group to the quotient. The existing
`IsUnipotent.of_iso` transports unipotence back to the original group.
Centrality and maximality beyond the fact that the domain is a torus are
not needed for this deduction.

In the finite-field clause, the geometric existence premise supplies an
actual torus inclusion whose algebraic-closure base change is maximal.
The no-torus hypothesis makes its range bottom over the original field.
`SubgroupFunctor.range_baseChangeHom` and `bot_baseChange` give the same
condition after extension. The published geometric connectedness theorem
supplies connectedness of the base change; smoothness and affineness are
preserved by pullback. The algebraically closed structural premise therefore
gives unipotence of this base change. `IsUnipotent.of_baseChange` reflects
unipotence to the original affine group scheme.

This is an internal deduction from the existing actual subgroup, quotient,
base-change and unipotence interfaces. It implements the reductions described
in the statement's Markdown, following the nilpotent and finite-field
paragraphs of Milne, *Algebraic Groups* (2017), Proposition 17.81, printed
p.379 (one-based PDF p.395), source ID `milne-2017-algebraic-groups`.
The proof uses neither the parent no-torus proposition nor preservation of
maximal tori under field extension. The nilpotent clause permits all fields;
the finite-field clause retains its finite-field premise. Both have arbitrary
universe `u` and no characteristic restriction.
