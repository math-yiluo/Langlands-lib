# Open comparisons of locally ringed colimits

This internal adapter combines the presheafed section comparison and the
topological cartesian-subdiagram criterion. It applies to arbitrary supplied
colimit cocones. It does not construct the global scheme pushout.

## Presheafed spaces

The indexing category has independent object and morphism universes. As in
`IntegralSchemePushoutGluing`, the coefficient category has object universe
`u + 1` and morphism universe `u`, and the spaces have universe `u`. Colimits
of the indexing shape in topological spaces and opposite-indexed limits in
the coefficient category are explicit typeclass premises.

`PresheafedColimit.comparisonIso` identifies Mathlib's chosen colimit with the
point of any supplied colimit cocone by uniqueness of colimits.

`PresheafedColimit.isOpenImmersion_colimMap_of_cartesian` assumes component
open immersions and, for every arrow `f : j ⟶ k`, the range identity

`(G.map f).base ⁻¹' range (τ_k.base) = range (τ_j.base)`.

After forgetting to topological spaces, the preceding topological helper gives
an open embedding of colimits and exact saturation. The presheafed section
comparison then makes the induced colimit map an actual open immersion.

`PresheafedColimit.isOpenImmersion_of_cartesian` gives the same conclusion
for a map `q` between two supplied colimit cocone points which commutes with
all cocone legs. Conjugating `q` by `comparisonIso` identifies it with
`colim.map τ`; composition with these isomorphisms preserves open immersions.

## Locally ringed spaces

`LocallyRingedColimit.forgetToPresheafedSpace` abbreviates the composite of
the standard forgetful functors through sheafed spaces.

`LocallyRingedColimit.isOpenImmersion_of_cartesian` applies the presheafed
criterion to this forgetful functor. Its explicit premises are the topological
colimits and opposite-indexed ring limits, preservation of the two diagrams'
colimits by the composite forgetful functor, two supplied colimit witnesses,
a commuting comparison `q`, componentwise locally ringed open immersions,
and the same cartesian range condition on the underlying continuous maps.
Mathlib supplies these size and preservation conditions for the finite span
diagrams used in the intended application.

`LocallyRingedColimit.range_of_cartesian` proves, under the same premises,
that `range (τ_j.base)` equals the inverse image of `range q.base` under each
large cocone leg. It applies the topological helper to the twice-forgotten
colimit cocones.

All results are internal consequences of Mathlib's colimit and open-immersion
APIs and the preceding project helpers. No additional source theorem is
asserted. The compatible affine neighborhoods, affine pushout model, scheme
structure, and exact integral scheme pushout statement remain separate
obligations.
