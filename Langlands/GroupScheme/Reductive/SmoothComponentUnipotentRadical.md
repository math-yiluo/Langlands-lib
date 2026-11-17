# Represented radicals and smooth identity components

This internal derived module works over an algebraically closed field in
arbitrary universe `u`. The ambient group `G` is smooth and may be nonaffine,
disconnected, or not quasi-compact. All radicals use the existing full
`IsUnipotentRadical` predicate and actual inclusion homomorphisms.

`IsUnipotentRadical.comp_smoothComponentInclusion` proves that a supplied
radical `i` of the actual smooth identity component remains a radical after
composition with its inclusion into `G`. Closedness is preserved by composition,
and smoothness, connectedness and fixed-vector unipotence are unchanged because
the source is unchanged. Normality follows from normality of the identity
component and the nonaffine smooth ambient action on its supplied radical.
For greatestness, every smooth connected normal unipotent closed competitor in
`G` factors through the actual identity component. The factor is closed by
closed-immersion cancellation. Normality of its full range follows by applying
the original normality to the included points and cancelling the monic component
inclusion. The component radical's greatestness then gives the required
containment after inclusion, on every relative test scheme.

`IsUnipotentRadical.smoothComponentSourceIso` compares any supplied radical
`i : U ⟶ G` with any supplied radical `j : V ⟶ G⁰` by an actual group-scheme
isomorphism `U ≅ V`. Uniqueness of radical image functors and the existing
closed-representative comparison construct it. Its inclusion equation is
`e.hom ≫ j ≫ inclusion G = i`.

`baseChange_of_smooth_component` reduces preservation of a supplied ambient
radical to preservation of a supplied radical in the identity component.
For an arbitrary extension of algebraically closed fields, the actual smooth
identity component commutes with base change. Ambient isomorphism transport
therefore turns the hypothesized base-changed component radical into a radical
in the identity component of the extended group. The first theorem gives a
radical of the full extended group. Applying actual base change to the source
comparison isomorphism and its inclusion equation transfers the entire radical
predicate to the original base-changed inclusion.

The proof uses the internal smooth identity-component construction and its
normality and base-change comparison, the generalized smooth radical action,
and published radical isomorphism transport and image uniqueness. It does not
assert existence of a radical in an arbitrary smooth connected nonaffine group,
or unconditional field-extension preservation.
