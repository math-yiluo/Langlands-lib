# Connectedness after field extension

`Langlands.AlgebraicGeometry.algClosedConnected` proves
`Langlands.AlgebraicGeometry.AlgClosedConnectedStatement.{u}`. A connected scheme
locally of finite type over an algebraically closed field is geometrically
connected. The theorem is uniform in the universe and the characteristic and
assumes no reducedness, smoothness, or properness.

The private topological lemma considers an open surjection `p : X → Y`, with
`Y` connected and Jacobson, and assumes that inverse images of closed points
are preconnected. Surjectivity first supplies a point of `X`. Given a cover
of `X` by two nonempty open sets, their open images cover `Y`. Connectedness
of `Y` makes these images intersect; the Jacobson property supplies a closed
point in that open intersection. Its inverse image meets both open sets,
and preconnectedness supplies a point in their intersection. This proves
connectedness of `X`.

The second private lemma treats the inverse image of a rational point
`e : Spec K ⟶ X`, with `e ≫ f = 𝟙`, under the field-extension projection
`p : X ×_K Spec L ⟶ X`. It constructs the map `j : Spec L ⟶ X ×_K Spec L`
and an explicit isomorphism
`pullback p e ≅ Spec L`. The inverse maps are proved equal using the
universal properties of the two pullbacks. Thus `pullback p e` is connected.
Its first projection has image `p ⁻¹' Set.range e`, so this inverse image
is connected by continuity.

For the main theorem, local finite type makes `X` Jacobson. Mathlib's
field-extension criterion reduces geometric connectedness to connectedness
of `X ×_K Spec L`. A morphism `Spec L ⟶ Spec K` is surjective, and is
universally open by Mathlib's instance for an integral singleton target;
these properties pass to `p`. Every closed point `x` of `X` is rational
because `K` is algebraically closed and `f` is locally of finite type.
The range of its rational point morphism is exactly `{x}`. The second
lemma therefore proves preconnectedness of every closed-point inverse
image. The first lemma concludes the argument.

This is an internal derivation using the pinned Mathlib's rational closed-point
comparison, universal openness, Jacobson closed-point existence, and scheme
pullbacks. It supplies geometric connectedness for the eventual connected
torsion closure; it proves no numerical torsion formula, dimension comparison,
or density assertion.
