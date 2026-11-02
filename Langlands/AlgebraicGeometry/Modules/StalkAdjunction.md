# Module stalks and skyscrapers

This internal supporting construction works for every scheme `X : Scheme.{u}`
and every point `x : X`. It lifts the actual abelian-group stalk of a module
sheaf to a functor `stalkFunctor x` to modules over the actual local ring
`X.presheaf.stalk x`, with the canonical action from Mathlib. Its map on
morphisms is the linear stalk map constructed in `RelativeFlatness`.

For a module `N` over that local ring, `StalkAdjunction.skyscraper x N` is an
actual module sheaf on `X`. Its sections on an open `U` are functions from
`PLift (x ∈ U)` to `N`; this is the zero group when the point is absent.
The ring of sections on `U` acts through its germ homomorphism to the local
ring. Restriction is restriction of the argument witnessing membership.
`presheafIso` identifies the underlying abelian presheaf with Mathlib's
usual skyscraper presheaf, and transports its sheaf condition. Linear maps
act pointwise, defining `skyscraperFunctor x`.

`StalkAdjunction.adjunction x` constructs the adjunction
`stalkFunctor x ⊣ skyscraperFunctor x`. A linear map from the stalk gives a
sheaf map by first taking germs. Conversely, a skyscraper-valued sheaf map
is evaluated on each neighborhood of `x`; these evaluations form a cocone
and induce an additive map from the stalk colimit. Representing a scalar
and a section on a common neighborhood proves that this induced map is
linear over the local ring. The germ formulas show that the two maps on
hom sets are inverse and natural in both variables, yielding the
adjunction. Thus all maps retain the actual section and stalk actions.

The provenance is internal: this is an explicit module-valued refinement
of Mathlib's abelian stalk and skyscraper constructions, derived from the
neighborhood-colimit universal property. It provides infrastructure for
comparing ordinary module pullback on stalks. It asserts no pullback
comparison, relative-flatness preservation, or coherent-family groupoid;
those are subsequent parts of the host construction. No quasi-coherence,
finiteness, noetherianity or quasi-compactness hypothesis is used.
