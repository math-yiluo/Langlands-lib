# Actual Weil reciprocity and its character comparisons

`Langlands.LocalClassField.weilReciprocityTheorems` proves all six
conjuncts of `WeilReciprocityTheorems.{u}` for every prime, every
`PadicField.{u} p` and each supplied `F.TopologicalData`. The five
conditional consequences take the published
`GeometricWeilReciprocityRelation` as their premise.

The first conjunct uses
`geometricWeilReciprocityExistenceUniqueness`. For the completion
conjunct, the profinite part of the candidate relation is the hypothesis
of `profiniteReciprocityCompletion` for `candidateGaloisHom`. This gives
the unique continuous equivalence agreeing with that map on the image
of `LocalMultiplicative.completionMap T`. Extensionality turns its
pointwise comparison into the equality of bundled homomorphisms in
`CompletionComparisonRelation`. Evaluation of any other such diagram
gives the pointwise equations for the same uniqueness theorem.

The inertia proof compares subgroup membership on elements of the form
`e w`, which exhaust the field multiplicative group. Membership in
`WeilQuotients.inertia` is zero descended degree. Membership in
`T.unitSubgroup` is zero normalized order. The geometric order component
identifies these conditions. The equality `WeilQuotients.inertia_eq_image`
then identifies the image of actual Weil inertia under the quotient map
followed by `e` with `T.unitSubgroup`.

For a continuous complex quasicharacter `χ`, the transported value on
`e (π w)` is `χ w`, where `π` is the actual closed-commutator quotient
projection. This follows from `e.symm (e (π w)) = π w` and evaluation
of the abelianization lift. The image of inertia and the level-zero
unit-filtration identities give the equivalence of the two triviality
conditions. Surjectivity of `π` and `e` lets the proof evaluate at
`e (π w)` for any element of `F.Carrierˣ`. The degree character gives `z ^ deg(w)`,
which equals `z ^ T.ord (e (π w))` by geometric order. Evaluating the
product of characters pointwise gives the twist formula for every `χ`
and every `z : ℂˣ`.

For the norm character, the same evaluation gives `q^(-deg(w))`,
where `q` is the canonical residue cardinality. The published
`residueCardinality_eq_canonical` identifies it with the supplied
`T.residueCardinality`. The order identity and the formula for
`T.normalizedAbs` on nonzero elements now give the equality after
casting the real integer power to `ℂ`. In particular, geometric
degree one gives `q⁻¹`.

The mathematical conventions and original-source correspondence are
documented in the paired statement. The quotient and character
arguments here derive the transport formulas from the published
geometric reciprocity relations, with the convention of Tate §1.4.1
and the norm normalization of §1.4.6.
[WeilReciprocityStatement](WeilReciprocityStatement.md)
