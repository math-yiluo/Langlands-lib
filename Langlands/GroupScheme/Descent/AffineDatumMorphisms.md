# Morphisms for the constructed affine descent solutions

This module is an internal consequence of the implemented affine group-scheme
effectivity construction and fpqc homomorphism descent. It works in arbitrary
universe `u` with actual schemes, group schemes, Čech data, and morphisms. All
compatibility equations are equations of actual group-scheme morphisms on the
overlap, so they retain every test scheme, including nonreduced tests.

## Morphisms between solutions

For a flat, surjective, quasi-compact morphism `p : S ⟶ B`, the first part
considers solutions `s` and `t` of actual data `D` and `E`.
`Solution.hom_ext` detects equality of morphisms between the descended objects
after pullback and composition with `t.iso.hom`. Its proof cancels this
isomorphism and uses faithful slice pullback.

`descendHom_id` and `descendHom_comp` prove that the previously constructed
`Solution.descendHom` preserves identities and composition. Both apply its
implemented uniqueness theorem and check the pullback equation.

`Solution.descendIso` applies homomorphism descent to a compatible
isomorphism and its compatible inverse. Faithful pullback, together with the
two recovery equations, proves the inverse identities. The result is an
actual isomorphism of the descended group schemes.
`baseChange_descendIso` compares it to the original isomorphism using both
solution identifications.

For two solutions of one datum, `comparison` descends the identity on the
original group. `comparison_hom` proves that this comparison respects the
original pullback identifications. `existsUnique_comparison` proves that
there is exactly one such actual isomorphism; it applies `hom_ext` to its
homomorphism. This gives uniqueness of the descended object with its
specified identification.

## An arrow to an original target

Let `C` be any group scheme over `B`, and let
`f : G ⟶ (baseChange p).obj C` be compatible from `D` to the canonical datum
on the pullback of `C`. `Solution.descendTo` descends this arrow using the
tautological solution for the target. It supplies an actual homomorphism
`s.obj ⟶ C`, with recovery equation

```text
(baseChange p).map (s.descendTo C f hf) = s.iso.hom ≫ f.
```

`existsUnique_descendTo` proves its uniqueness. The target need not be
affine. `comparison_hom_descendTo` proves that replacing the solution of the
source changes the descended arrow by the unique canonical comparison.
This proof checks equality after faithful pullback and then uses the
comparison and recovery equations.

## Constructed affine morphisms

Now assume `B`, `S`, and the underlying source group schemes are affine,
and `p` is flat and surjective. Quasi-compactness follows from the affine
hypotheses. `Datum.affineHom` and `Datum.affineIso` compose the preceding
constructions with `Datum.affineSolution` on both ends. They construct
actual morphisms and isomorphisms from compatible affine data without a
supplied solution.

For a target `C` already over `B`, `Datum.affineHomTo` constructs an actual
arrow from the constructed affine group to `C`.
`baseChange_affineHomTo` proves the recovery equation above, with
`s = D.affineSolution`. `existsUnique_affineHomTo` proves that the arrow
is unique. The only source-side inputs are the actual affine datum and the
compatible arrow; object effectivity and arrow descent are conclusions.
No field, finite-type, smoothness, reducedness, or commutativity assumption
is imposed.

## Provenance and remaining obligations

The module derives its constructions and proofs from
`Descent.AffineDatumGroup`, `Descent.FpqcHomDescent`, and the original actual
datum interface in `Descent.Data`. It invokes no new literature assertion or
unproved existence statement.

In the simply connected cover construction, `affineHomTo` can descend a
compatible covering map once its source datum has been constructed.
This module does not construct that datum or prove semisimplicity, simple
connectedness, central isogeny, or the central-cover universal property.
Those properties remain separate obligations of the host existence proof.
