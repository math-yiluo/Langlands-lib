# A same-apartment chamber from incident root restrictions

This derived internal unit connects nonzero composites of actual torus
morphisms with the coefficient-fixed direction and regular-facet criteria
in `UnramifiedSplitTorusFixedDirections` and
`UnramifiedSpecialApartmentRegularDirectionReduction`. It uses their
constructions without introducing a further literature assertion.

Let k and K be fields in a common universe with a supplied k-algebra
structure on K. Supply commutative group schemes T and S over k, an affine
group scheme G over k, a morphism `i : T.toGrp ⟶ G`, a splitting proof
`hS : IsSplitTorus S.toGrp`, and a specified morphism `f : S ⟶ T`.
Write `T_K`, `i_K`, and `f_K` for their actual coefficient pullbacks.

`exists_galois_fixed_direction_of_root_comp_ne_zero` takes an actual relative
root a of i_K and the raw nonvanishing hypothesis `f_K ≫ a.val ≠ 0`.
The additive rational-character restriction along `groupHom f_K` is
definitionally this same composite, with the same zero morphism.
The existing split-torus direction theorem therefore gives a vector in
the actual reduced translation space fixed by every coefficient
automorphism `K ≃ₐ[k] K`, on which the root form is nonzero.

Assume the underlying scheme map of i_K is monomorphic and supply an
actual `KPApartmentData` D for i_K and any order map on K units.
`hasIncidentGaloisDirections_of_root_comp_ne_zero` takes a point p in D
and requires the raw nonzero composite for every a that is the derivative
of an ordinary affine root of D vanishing at p. It converts this premise
definitionally and applies the existing incident-direction theorem.
The result is `HasIncidentGaloisDirections k K i D p` for this same D.

For the chamber construction, supply an integer-valued valuation v on K
and an actual apartment D' for its order map. Additionally supply connected
reductivity `hG` of the actual coefficient extension of G, maximal
splitness `hi` of i_K, a centralizer datum C, the full proof
`h6 : IntegerValuation.IsOmegaCompatible v D' C`, and coefficient stability
`hD : GaloisStable k K i D'`. Supply a point p fixed by every actual affine
coefficient automorphism, with an explicit proof hp, and raw nonzero
composites for every ordinary derivative root incident to p.
None of these assumptions is inferred from the existence of p.

`exists_regular_galois_stable_facet_of_root_comp_ne_zero` composes the
incident-direction adapter with
`exists_regular_galois_stable_facet_of_directions`. It produces a point x
in D' regular for its ordinary affine roots such that the whole ordinary
sign facet through x is preserved setwise by every actual affine
coefficient automorphism. `incidentRootChamberPoint` chooses such a point
as a subtype retaining regularity and this full-facet invariance.
The only choice is from that proved existential in the supplied D'.

The unit is uniform in its universe and imposes no field or residue
characteristic restriction. It applies in particular to the maximal
unramified extension in the special-apartment chamber problem. It does
not establish the incident-root nonvanishing premise, existence of
recovered integral models, or the exact chamber target unconditionally.
