# Generalized eigencharacter detection in actual graded quotients

Authors: Worker 573 and Worker 846. Worker 573 wrote the Lean proof and
its first explanation; Worker 846 checked it, renamed one helper to avoid a
Library name collision and revised this explanation.

`Langlands.generalizedEigencharacterFiltration` proves
`Langlands.GeneralizedEigencharacterFiltrationStatement`, with independent
ring, monoid, representation-carrier and category universes. It concerns
the existing actual `RepFunctorFiltration` and its actual quotient objects.
The restricted action uses the supplied monoid homomorphism.

The proof takes a nonzero vector in the ambient uniform character space.
It cannot belong to the zero first step and belongs to the full last step.
Induction over `Fin (n + 1)` therefore finds consecutive steps containing it
above and not below. Its class in their actual successive quotient is
nonzero, by the quotient's zero criterion. The monotonicity field of the
filtration is not needed: the denominator of that quotient is the lower
step pulled back to the upper one, which does not contain the vector.

The same vector in the invariant upper step satisfies the same
character-defect equations. The helper
`mem_characterSpace_subrepresentation_comp` proves this by applying
Mathlib's `Module.End.genEigenspace_restrict`, the generalized eigenspace
formula for the restriction of an endomorphism to an invariant submodule,
to each monoid element. The actual quotient projection is an intertwiner
after restriction along the monoid homomorphism.

`map_mem_characterSpace_of_intertwiningMap` applies Mathlib's
`Module.End.mapsTo_genEigenspace_of_comp` to each monoid element. It
preserves exactly the supplied finite exponent, and hence takes the upper
vector into the same character space in the graded quotient. The nonzero
quotient image proves that space nonzero. This argument needs neither
simple factors nor a field, and includes repeated steps, zero graded
pieces and length zero. The helper's name differs from the Library's
`Langlands.map_mem_characterSpace`, a different result about stability of a
character space under a commutative action.

The module also provides
`RepFunctorFiltration.exists_graded_isGeneralizedEigencharacter` by
unpacking the existential finite exponent and applying the closed theorem.
`isGeneralizedEigencharacter_of_map_ne_zero` detects the character whenever
an intertwiner's image of a supplied generalized vector is nonzero.
`isGeneralizedEigencharacter_iff_of_equiv` applies this in each direction
of an actual representation equivalence. The main theorem does not use
this last helper.

This is an internal linear-algebra deduction from the published
`characterSpace`, filtration and quotient definitions and the pinned
Mathlib eigenspace lemmas. It constructs no geometric filtration and
establishes no refined-induction spectrum extension, chamber inequality,
modulus comparison or temperedness theorem.
