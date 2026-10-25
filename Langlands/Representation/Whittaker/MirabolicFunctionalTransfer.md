# Functional spaces under actual mirabolic restriction

This internal adapter supplies the functional-exactness inputs for restricting
a representation of `GL_(n+1)(F)` to the actual mirabolic subgroup. Field and
representation-carrier universes remain independent.

`character_isLocallyConstant_of_hasFunctional` applies to any topological
group and a smooth complex representation. Choose a nonzero equivariant
functional and a vector on which its value is nonzero. On the subgroup, the
character equals the corresponding matrix coefficient divided by that fixed
nonzero value. The published local constancy of smooth matrix coefficients,
continuous restriction to the subgroup, and division by a constant give local
constancy of the character's scalar values. No continuity hypothesis on the
character is needed.

`mirabolicFunctionalsEquiv` identifies the full functional spaces before and
after restriction. It uses the published upper-unipotent group identification
and composes the character with that identification. Both directions leave
the underlying linear functional unchanged; their covariance conditions agree
on the actual matrices. It applies to every character, so in particular to
both the standard and inverse characters. The representation carrier is
unchanged.

`GeneralLinear.Mirabolic.upperUnipotent_isLimitOfCompactSubgroups` transports
the published compact-containment result for the upper-unipotent subgroup
of GL through its continuous group equivalence with the upper-unipotent
subgroup of the mirabolic group. A compact set has compact image; a compact
subgroup containing that image pulls back to a compact subgroup containing the
original set. The argument uses exactly the supplied field topology.

`mirabolic_existsUnique_hasFunctional_factor` assumes a smooth GL
representation, a linear equivalence of its full functional space with the
complex numbers, and an actual finite filtration of its mirabolic restriction.
Restriction is smooth by continuous pullback, and the functional equivalence
transports by `mirabolicFunctionalsEquiv`. This equivalence supplies a nonzero
functional, so the local-constancy lemma applies. Compact containment and
`Whittaker.existsUnique_hasFunctional_factor` then give a unique graded
position admitting a nonzero functional for the transported character.

The provenance is internal transport of published constructions and
functional-length exactness. The result counts actual positions, including
multiplicities. It neither constructs a finite mirabolic filtration nor
identifies its unique functional-bearing factor with compact induction.
It applies in rank one and does not assume irreducibility or a central
character.
