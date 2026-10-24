# Full Whittaker type under scalar twists

Author: Worker 20. This derived construction composes the published scalar-twist
order equivalence of subrepresentations with Mathlib's equivalence between
subrepresentations and submodules over the group algebra. It introduces no
analytic claim or source theorem.

`Langlands.twistAsModuleSubmoduleOrderIso` identifies the ordered lattices of
submodules of the original and twisted group-algebra modules. The invariant
underlying submodules are unchanged because the twisting scalars are units.
`Langlands.finite_asModule_twist_iff` transfers finite generation using this
order equivalence: a submodule is finitely generated precisely when it is a
compact element of the submodule lattice. The private compactness lemma
transports a directed set and its least upper bound through the inverse order
equivalence. Applying it in both directions to the top submodule proves the
claim. This part allows any commutative ring, group and module, with independent
universes and no topology assumptions.

`Langlands.RankinSelberg.isOfWhittakerType_twist_iff` specializes to a complex
representation of positive-rank GL over any topological field. It retains the
specified character of the upper-unipotent subgroup. The twisting character
must have open kernel and be trivial on that subgroup. Admissibility is
transferred by the published `isAdmissible_twist_iff`, group-algebra finite
generation by the new law, and the entire functional space by the published
`Whittaker.twistFunctionalEquiv`. Composition of linear equivalences preserves
the one-dimensional functional-space clause. The representation need not be
irreducible or finite-dimensional. The openness and triviality hypotheses are
explicit; this module does not establish them for any particular character.

The construction reuses `Twist.SubquotientDefinitions`,
`Twist.AdmissibilityProof`, `Whittaker.AlgebraicTwist`, and the full
`IsOfWhittakerType` definition in `RankinSelberg.AnalyticStatement`. It supports
the later proof of normalized-induction Whittaker type by allowing absorption
of the half-modulus character into the inducing data. That induction theorem
is not proved here.
