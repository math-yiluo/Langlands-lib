# Renard A.III.2: Yoneda proof

Author: Worker 633.

This proof imports the unchanged public statement
`Langlands.CategoryTheory.Renard.YonedaStatements`. It proves its four clauses
and their complete conjunction, `Langlands.Renard.Yoneda.YonedaStatements`,
with independent value, morphism and object universes `w`, `v`, `u`.

The original source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, Appendix A.III.2, printed
pp.253–254 / one-based PDF259–260, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 633 read these original pages. They define the Yoneda functor and
representability, give the evaluation and Hom bijections, and state the
equivalence with the full subcategory of representable presheaves. This proof
uses Mathlib's implementation of that argument. The lifts and representation
dictionary are internal adapters for the published statement's universe
conventions.

`evaluationStatement` composes `uliftYonedaEquiv` for the lifted presheaf
`F ⋙ uliftFunctor` with the equivalence that removes `ULift`. Both displayed
map formulas follow by unfolding these equivalences.

`homEquivalenceStatement` uses the Hom equivalence of the actual fully faithful
lifted Yoneda functor. To verify the evaluation formula for an arbitrary natural
transformation, it uses surjectivity to write that transformation as the image
of an actual arrow, then uses the inverse law and the identity composition law.

`representationDictionaryStatement` composes the inverse of
`representableByUliftFunctorEquiv` with `RepresentableBy.equivUliftYonedaIso`.
The resulting equivalence of representation and isomorphism data gives both
directions after applying `Nonempty`.

`representableEquivalenceStatement` lifts the actual `uliftYoneda` functor into
the full subcategory defined by `Functor.IsRepresentable`. Fullness and
faithfulness are inherited by this lift. For each representable presheaf,
`reprX` and `uliftYonedaReprXIso` give a preimage up to isomorphism, and
`ObjectProperty.isoMk` realizes that isomorphism in the full subcategory.
`Functor.asEquivalence` then constructs the equivalence, and `liftCompιIso`
supplies the natural isomorphism from its composite with the actual inclusion
to the lifted Yoneda functor.

No smallness, nonemptiness, finiteness or equality between universe levels is
assumed. The later universal-property remark and compatible uniqueness in
A.III.2, and all other Appendix A assertions, remain outside this proof.
