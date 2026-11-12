# Regrouping coproducts by actual Bernstein inertial classes

This internal construction handles the regrouping step of the proof of
Renard VI.7.2, printed pp.181–184 / PDF pp.187–190, in the edition dated
9 July 2026. It uses the original `BernsteinInertialClass`,
`bernsteinBlockProperty` and `Renard.IsCoproductOfComponents`.
It assumes the named actual support-uniqueness statement and a supplied
coproduct whose summands individually belong to labelled Bernstein blocks.
It proves neither input.

`bernsteinGroupedSubspace` groups all images of cofan legs with a fixed class
label by taking their invariant supremum inside the original cofan vertex.
Consequently each grouped component retains the vertex's carrier universe,
even when the original index type or the Bernstein quotient is larger.
No existence of coproducts at either larger index universe is assumed.

Every irreducible subquotient of a grouped invariant supremum occurs in one
image summand by the published `irreducibleSubquotient_iSup`. That image is
a quotient of the original labelled object. Subquotient transitivity and
the label equality therefore give the exact original Bernstein block
property. The images of a colimiting cofan span the vertex, hence so do
their grouped sums.

`bernsteinGroupedCofanIsColimit` uses actual support uniqueness to exclude
common irreducible constituents of differently labelled grouped components.
The bundled `invariantSubspaceCofanIsColimit` then constructs the universal
property from spanning and independence. Finally
`isBernsteinCoproductOfComponents_of_labelledCofan` packages this cofan in
Renard's exact coproduct predicate.

The construction is derived from actual invariant sums and published
constituent helpers. It formalizes only the collection of already supplied
block summands. The finite cuspidal embedding, its Levi inertia decompositions,
induced-inertia block membership, support uniqueness and the unconditional
Bernstein decomposition remain separate obligations.
