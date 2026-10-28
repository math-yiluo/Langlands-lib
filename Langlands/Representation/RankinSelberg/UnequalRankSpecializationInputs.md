# Supplied-topology inputs for unequal-rank assembly

This internal construction extracts established inputs from the published
`RankinSelberg.IsOfWhittakerType` hypothesis. It applies to an arbitrary
character of the full upper-unipotent subgroup, so it covers both the standard
character on the larger representation and the inverse-standard character on
the smaller one. The field universe and representation-carrier universe remain
independent. Applying the helpers to the two representations imposes no relation
between their carrier universes.

`finiteLength_of_whittakerType` proves finite group-algebra length for the
original representation of `GL_(n+1)`. It uses the admissibility and finite
generation clauses of Whittaker type. The supplied topology is identified with
the canonical module topology by `TopologicalData.topology_eq_canonicalModule`,
and the public `Langlands.glAdmissibleFiniteLength` theorem then applies.

`mirabolicFunctionalEquivOfWhittakerType` chooses the functional-space
equivalence with the complex scalars supplied by Whittaker type, and composes
it with the inverse of `Whittaker.mirabolicFunctionalsEquiv`. Its source is
the full space of functionals on the actual mirabolic restriction, with the
character transported along `Mirabolic.upperUnipotentEquiv`. The representation
and its carrier are unchanged apart from restricting the acting group.

`mirabolic_smooth_and_character_locallyConstant_of_whittakerType` proves
smoothness of that restriction using the continuous subgroup inclusion. Its
functional-space equivalence makes its functional length one, hence gives a
nonzero functional. The public
`Whittaker.character_isLocallyConstant_of_hasFunctional` then proves local
constancy of the transported scalar character.
`character_locallyConstant_of_whittakerType` gives the corresponding result
on the original general linear group by the same nonzero-functional argument.
Neither result requires a continuity-to-local-constancy assertion for arbitrary
characters.

`generalLinear_compactOpen_cofinal` proves that every open subgroup of
`GL_(n+1)` contains a compact open subgroup for the supplied topology. It applies
the public block Iwahori neighborhood theorem to a single positive block and
the open subgroup's identity neighborhood, then forgets the factorization.
It holds for every natural `n`, including `n = 0`.

These are derived consequences of public Library declarations; no new
original-literature claim is transcribed. The module supplies finite length
only for the original general linear representation. Finite length of its
mirabolic restriction still needs its separate theorem. The source pairing
proofs, mixed finite-filtration assembly, source length bound, and full
unequal-rank uniqueness theorem are not proved here.
