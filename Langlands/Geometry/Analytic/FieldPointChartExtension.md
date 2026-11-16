# Fixed-target chart character extension

This internal construction is conditional on
`PresentedAffinoidAlgebra.DomainCompletedResidueSurjectivityStatement`.
It treats every affinoid atlas presentation over a complete ultrametric normed
field `K`, and every complete normed field `L` with a normed `K`-algebra
structure. The universes of `K`, the underlying space, the chart indices and
`L` are independent. No algebraic closedness or ultrametric assumption on `L`
is needed.

`IsChartCharacter x i g` means that a spectrum point of chart `i` maps to `x`
and its seminorm is the absolute value of the given `K`-algebra character `g`.
Precomposition with an atlas restriction gives a character in the containing
chart. The atlas restriction square proves its norm and underlying point
identities.

`existsUnique_chartCharacter_lift` extends such a character uniquely to any
smaller chart containing `x`. The restriction has the full domain property by
`restriction_represents`. The explicit domain residue hypothesis makes its
canonical completed-residue comap surjective. CharacterTransport then supplies
existence and uniqueness in the prescribed complete field `L`. Injectivity of
the chart embedding identifies the relevant spectrum points.

For the all-chart construction, an internal relation records characters on two
charts induced by one character on a common smaller chart through `x`. Given a
character on one chart, lift it to a chart contained in its intersection with
any other chart, then restrict that character to the other chart. This provides
existence. To compare two such choices, take a common refinement of their
smaller charts and lift both characters there. They have the same restriction
to the originally prescribed chart, so uniqueness of character extension
identifies them. Restricting to the desired chart proves independence. The
atlas restriction composition identity also shows that this relation is
preserved when passing to a larger chart.

`FieldPoint.eq_of_eval_eq` proves that two field-valued points with the same
underlying point and the same character on one containing chart are equal.
Their evaluations on every other chart satisfy the preceding common-refinement
relation, so uniqueness identifies them; `FieldPoint.ext'` finishes.

`FieldPoint.existsUnique_of_chartCharacter` constructs a unique field-valued
point with underlying point `x` and prescribed character `g₀` on chart `i₀`.
Choose the unique character related to `g₀` on each chart containing `x`.
Relation preservation and uniqueness prove the restriction compatibility.
The identity restriction identifies its value on `i₀` with `g₀`. The preceding
one-chart equality result proves uniqueness of the field-valued point.

All assertions here are internal deductions from the explicit domain residue
comparison premise, the character transport lemmas and the atlas axioms.
This module supplies no proof of domain residue comparison or of the étale
site point axioms.
