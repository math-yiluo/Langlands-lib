# Čech nerves under functors preserving their defining limits

This internal categorical construction compares the actual augmented Čech
nerve of an arrow after applying a functor with the augmented Čech nerve of
the image arrow. Its intended application is evaluation of set-valued
presheaves, where a surjective evaluated arrow has a section even when the
presheaf arrow has no natural section.

Let `A` and `D` be categories with independent object and morphism universes,
let `F : A ⥤ D`, and let `f : Arrow A`. For each natural number `n`, assume
that the wide pullbacks of `n + 1` copies of `f.hom` and of `F.map f.hom`
exist, and that `F` preserves the former defining wide-cospan limit. No
preservation of other limits is required.

`cechWideCospanCompIso` identifies the defining wide cospan followed by `F`
with the wide cospan of the mapped arrow. Its components are identity
isomorphisms. `cechTermMapIso` composes the preserved-limit isomorphism with
the limit isomorphism induced by this diagram comparison. The two projection
lemmas state that its forward map followed by any source projection, or the
base projection, equals the image under `F` of the corresponding original
projection.

`cechNerveMapIso` assembles these isomorphisms into an isomorphism of
simplicial objects. Naturality follows by the wide-pullback universal
property: both composites have the same source projections and base
projection, since the Čech simplicial operators reindex those projections.
`augmentedCechNerveMapIso` extends it to the augmented objects, using the
identity isomorphism on `F.obj f.right`. Its augmentation compatibility is
the base-projection formula in every degree.

Finally, `mappedCechExtraDegeneracy` takes a specified
`SplitEpi (F.map f.hom)` and transports Mathlib's extra degeneracy for that
split arrow across the inverse augmented comparison. Its output is an extra
degeneracy of the original augmented Čech nerve after applying `F`.
It does not require a section of `f.hom`.

The provenance is the defining wide-pullback universal property together
with Mathlib's preserved-limit comparison and its extra degeneracy of a
split epimorphism. No external mathematical source is claimed for this
internal adapter. This module does not establish free-module exactness,
locally surjective Čech exactness, analytic higher nerve presentations,
coefficient acyclicity or the analytic comparison theorem.
