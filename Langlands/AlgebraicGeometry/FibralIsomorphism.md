# The fibral isomorphism criterion

This module proves
`Langlands.AlgebraicGeometry.fibralIsomorphism :
Langlands.AlgebraicGeometry.FibralIsomorphismStatement.{u}` for every universe
`u`. It imports the published statement without modifying it.

For any scheme `S`, let `Y` and `Y'` be locally finitely presented schemes over
`S`, with `Y` flat over `S`, and let `h : Y ⟶ Y'` be an `S`-morphism. If its
base change to `Spec κ(s)` is an isomorphism for every point `s : S`, then
`h.left` is an isomorphism. The theorem adds no hypotheses to the published
statement.

## Source and provenance

The target is Brian Conrad, *Reductive group schemes* (2014), Lemma B.3.1,
printed/PDF p.288, registered as `conrad-2014-reductive-group-schemes`.
Conrad cites EGA IV₄, 17.9.5 and Exercise 3.4.3 for the proof. The source
correspondence and residue-field fibre convention are documented in the
unchanged [statement Markdown](FibralIsomorphismStatement.md).

The implemented proof uses the published
[`isOpenImmersion_of_fiberwise`](FiberwiseOpenImmersion.md) and Mathlib's
scheme-theoretic pullback point-lifting and surjective-open-immersion results.
Its direct surjectivity argument is the same general point-lifting argument
used for the diagonal in `FiberwiseOpenImmersion.lean`, applied here to `h`.

## Implemented proof

Every residue-field fibre of `h` is an isomorphism and hence an open immersion.
The source is flat and locally of finite presentation over `S`, and the target
is locally of finite presentation, hence locally of finite type.
`isOpenImmersion_of_fiberwise` therefore makes `h.left` an open immersion.

For surjectivity, take a point `y` of `Y'` and put `s = Y'.hom y`.
`Scheme.Pullback.exists_preimage_pullback` lifts `y` to a point `y'` of the
fibre of `Y'` over `s`, using the closed point of `Spec κ(s)` and
`Scheme.fromSpecResidueField_apply`. The fibre isomorphism is surjective, so
`y'` has a preimage `x'` in the fibre of `Y`. Projecting `x'` to `Y` gives a
preimage of `y`: the base-change square commutes by `pullback.lift_fst`, and
`Scheme.Hom.comp_apply` expresses this equality on points.

Finally, `isIso_iff_isOpenImmersion_and_surjective` makes the surjective open
immersion `h.left` an isomorphism. The proof applies to all points of an
arbitrary base scheme.
