# Comparison of actual homogeneous quotient models

Author: Worker 1478.

This internal derived construction works over every base scheme
`S : Scheme.{u}`, at arbitrary universe `u`. It starts with an actual relative
scheme `X`, relative schemes `Q,R`, and maps `q : X ⟶ Q`, `r : X ⟶ R`.
It does not construct a quotient or assume that its source is a group.

Suppose `q.left` is an effective epimorphism of schemes and every pair of
relative test maps with the same `q` image also has the same `r` image.
`scheme_comp_eq_of_fiber_eq` proves the corresponding implication for arbitrary
underlying scheme maps. Give the test scheme the structure map obtained by
composing its first map with `X.hom`; equality after `q` shows that the second
map has that same structure map. The relative hypothesis then applies.

`descSchemeHom` uses the effective-epimorphism universal property to descend
`r.left` through `q.left`. Cancelling the epimorphism `q.left` proves that the
descended map is over `S`; `desc` is this actual relative morphism. `fac_desc`
states `q ≫ desc q r h = r`. Cancellation also proves `desc_unique`.

If `r.left` is an effective epimorphism as well and the fibers agree on every
relative scheme test, `iso` descends in both directions. Composing with `q`
or `r` and cancelling proves the two inverse identities. The comparison
isomorphism satisfies `comp_iso_hom` and `comp_iso_inv` and is unique by
`iso_unique`.

For any fixed relative test scheme `T`, `forall_lifts_iff` transports every
point across this comparison isomorphism, lifts it using the other projection,
and retains that same map from `T` to `X`. Thus surjectivity on actual
`T`-valued points is independent of the quotient model. In particular
`T = Over.mk (𝟙 S)` gives the section, or field-rational-point, case.
No residue-field or topological-point replacement occurs.

The effective-epimorphism hypotheses apply in particular to flat, surjective,
quasi-compact maps, by Mathlib's fpqc instance imported by this module.
When two supplied homogeneous quotient models have the same all-test
right-coset condition, composing those equivalences supplies the fiber
equivalence required here. All tests are retained, including nonaffine and
nonreduced schemes.

The provenance is internal: Mathlib's effective-epimorphism universal property,
its fpqc instance, the slice-category structure and category laws. This unit
handles comparison of supplied quotient models; it proves no unconditional
rational-lifting, quotient-existence, pseudo-parabolic-structure or
local-sections theorem.
