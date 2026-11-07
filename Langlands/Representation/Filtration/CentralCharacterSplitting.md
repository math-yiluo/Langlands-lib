# Splitting finite filtrations with distinct central characters

Author: Worker 1739.

This module implements the lemma inside the proof of Renard VI.8.5, printed
p.194 / PDF p.200, in the French edition dated 9 July 2026. The registered source
is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Renard states that a finite filtration with distinct central characters splits
as a direct sum of its successive quotients. Here the coefficient field is any
infinite field, including the source's complex coefficients. The field, group,
and vector-space universes are independent.

For a representation `A` and an actual filtration `s : ObjectRepFiltration A n`,
`HasCentralCharacterSplitting s χ` records three conclusions: each scalar
central-character subrepresentation `centralCharacterSpace A.ρ (χ i) 1` is
equivalent to the actual quotient `s.gradedRepresentation i`; their underlying
submodules form an independent family; and every invariant subspace `S` is the
supremum of its intersections with these subrepresentations.
`splitting_of_distinct_centralCharacters` proves this property when `χ` is
injective and every central group element acts on quotient `i` by `χ i`.
`iSup_centralCharacterSpace_eq_top` gives the full-space decomposition by taking
`S = ⊤`. Together with independence and the quotient equivalences, this expresses
the direct-sum conclusion of the source. The hypotheses permit zero quotients
and the empty filtration; no irreducibility, admissibility, topology, or finite
vector-space dimension is required.

The group-algebra constructions and the invariant-subspace conclusion are
internal elaborations of the source argument. `algebraRepresentation` extends
the group action to the multiplicative monoid of `MonoidAlgebra k G`.
`algebraSubrepresentation` keeps the same underlying submodule, and
`algebraFiltration` keeps the same filtration spaces and actual quotient vector
spaces. `algebraFiltration_graded_action` proves that its quotient action is the
group-algebra extension of the original quotient action: the quotient projection
intertwines group elements, hence their finite linear combinations.

For a finitely supported coefficient function `t` on the center,
`centralAlgebra t` is the corresponding linear combination of group-algebra
basis elements, and `characterValue χ t` is the corresponding scalar evaluation.
Central group elements commute with all group elements, so `centralAlgebra t`
commutes with every group-algebra element. Scalar central action extends to
these linear combinations by `centralAlgebra_acts_scalar`.

`exists_separating_centralAlgebra` applies Mathlib's finite-union avoidance
lemma `Module.Dual.exists_forall_ne_zero_of_forall_exists` to all pairwise
differences of the character-evaluation linear forms. Distinct characters make
each such difference nonzero on a basis vector. Over an infinite field, one
coefficient function therefore makes all scalar evaluations distinct. The
resulting separating operator is a finite linear combination; the proof does
not require a single central group element with distinct character values.

The proof then applies the published `CentralEigenspaceSplitting` construction
to the extended filtration and this central operator. Its eigenspaces are
independent, each projects bijectively onto its corresponding actual quotient,
and they split every invariant subspace. Regard an eigenspace as an original
group subrepresentation. The quotient projection is still intertwining and
injective there, so the scalar action of every central group element on the
quotient lifts to that eigenspace. Conversely, a vector with the specified
scalar central character has the specified eigenvalue for the separating
linear combination. Thus these auxiliary eigenspaces equal the original scalar
central-character subrepresentations, giving all three conclusions.

This is a filtration lemma used in the source proof of VI.8.5. It does not by
itself prove generic irreducibility or the geometric and unitarity inputs to
that theorem.
