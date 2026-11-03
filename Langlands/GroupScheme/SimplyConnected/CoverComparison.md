# Comparison of actual central covers over isomorphic field groups

Worker 416. This internal construction works over an arbitrary field
`k : Type u`. Its inputs are actual group schemes, actual homomorphisms
`π : C → G` and `π' : C' → G'`, the supplied cover properties, and a
specified isomorphism `e : G ≅ G'`. All groups have the same field base.

`HasCentralCoverUniversalProperty.comp_iso` transports the universal
property from `π` to `π ≫ e.hom`. For an incoming semisimple central
isogeny `q : H → G'`, postcompose with `e.inv` and use the original
universal property. Composing the factorization equation with the
isomorphism gives the desired equation over `G'`; composing any other
factorization with its inverse proves uniqueness.
`HasCentralCoverUniversalProperty.iso_comp` transports the universal
property under an isomorphism of the supplied source. It precomposes
the original factorization with that isomorphism, and applies its inverse
to any competing factorization.

`IsSimplyConnectedCover.comp_iso` and `.iso_comp` combine these laws with
the existing isomorphism invariance of semisimplicity, simple connectedness,
and central isogenies. They transport the complete predicate about an
actual supplied cover.

The selected construction `IsSimplyConnectedCover.isoOver` produces an
actual isomorphism `C ≅ C'` lifting `e`. Postcompose `π'` with `e.inv`,
making it a cover of `G`, and apply the existing canonical comparison of
two covers of the same target. `isoOver_hom_comp` proves the exact equation

```text
(isoOver hπ hπ' e).hom ≫ π' = π ≫ e.hom.
```

`hom_eq_isoOver` proves that any actual homomorphism satisfying this
equation is the canonical comparison, by the first cover's universal
property applied to `π' ≫ e.inv`. `existsUnique_lift_iso` packages existence
and uniqueness of that homomorphism. `hom_ext_over_iso` only requires the
first full cover, a semisimple second source, and a central second map;
it identifies any two homomorphisms lifting the specified target
isomorphism by the same argument.

Provenance is internal: every step is a deduction from the explicit
universal property and the existing isomorphism transport lemmas in
`SimplyConnected.Basic` and `CentralIsogeny.Transport`. No cover existence
theorem is invoked. This module proves no preservation under extension
of the field or under an isomorphism of base schemes. In a descent
application, the cover properties of the actual groups on each field
component must first be supplied; no field-only predicate is applied to
a tensor overlap which is not a field. The arbitrary-field extension
theorem remains a separate obligation.
