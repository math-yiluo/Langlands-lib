# One additive equation for a proper closed vector subgroup

This internal construction turns a proper closed embedding of a corepresented
group into a standard vector group over any field into one nonzero row of
additive one-variable polynomials that annihilates the embedding as an actual
group-scheme homomorphism. The source may be nonreduced, disconnected or
nonsmooth. No characteristic, infinitude or perfection hypothesis is imposed.

Fix a field `k`, a group-valued functor `F` on commutative `k`-algebras with
corepresentation `e` by `B`, and a group-scheme homomorphism
`q : Corepresented.groupScheme F e ⟶ VectorGroup.groupScheme k n`.
`coordinatePullback` recovers the algebra map from `q` using the fully faithful
affine spectrum functor. `coordinateFamily` is the image of the standard
linear variables under that map. `affine_coordinates` identifies these
elements on every algebra-valued point, and `coordinateFamily_primitive`
deduces their additivity from the fact that `q` preserves multiplication.
`eq_quotientMap` identifies `q` with the published homomorphism constructed
from this primitive family.

If the underlying scheme map of `q` is a closed immersion,
`coordinatePullback_surjective` transports surjectivity of its global-section
pullback through the canonical spectrum/global-section isomorphisms. A
bijective coordinate pullback gives a spectrum isomorphism, and reflection of
isomorphisms through the forgetful functors gives `IsIso q`.
Consequently, if `q` is not an isomorphism, subtracting two distinct elements
with the same image supplies a nonzero polynomial relation.
`exists_additive_equation` applies the published
`PrimitivePolynomial.exists_additive_relation` to this relation and to the
primitive family in the canonical bialgebra associated to `e`.

`exists_annihilating_polynomialRow` separates the resulting multivariate
additive polynomial into its one-variable parts using
`TorusLinearization.IsAddPoly.eq_sum_part`. Universal additivity of each part
gives `Unipotent.OneDimensional.IsAdditive`. At least one part is nonzero,
since otherwise the original polynomial would vanish. Finally,
`comp_polynomialRow_eq_zero` evaluates the separated relation on every relative
scheme test through the spectrum/global-section adjunction and concludes
`q ≫ Unipotent.polynomialRow f hf = 0` by pointwise extensionality. This
includes nonreduced scheme tests and is not limited to field-valued points.

The provenance is internal: the contribution assembles the existing
corepresented-point, primitive-relation, additive-polynomial and polynomial-row
interfaces. It supplies one equation and does not assert that additive
polynomials generate the defining ideal, nor construct a vector factor or a
complement. Those structural conclusions remain obligations of the host
vector-factor task.
