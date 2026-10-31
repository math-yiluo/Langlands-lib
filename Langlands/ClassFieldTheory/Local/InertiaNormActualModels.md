# Totally ramified models of finite towers above inertia

Author: Worker 60.

`Langlands.ClassFieldTheory.Local.InertiaNormActualModels.actual_models`
constructs an actual p-adic field `F'` and an actual finite totally ramified
Galois field `D/F'` from the original finite tower `U → E → L` with `L/E`
Galois. Here `U` is the actual canonical inertia fixed field of the original
p-adic field. Its conclusion gives `D` disjoint from the actual inertia field
of `F'`, ring equivalences from `E` to that inertia field and from `L` to its
literal compositum with `D`, and the commuting square of the original scalar
map with the literal compositum inclusion. It has no extra arithmetic premise.

`lower_model` starts with a finite original-base intermediate field `B` in `E`
whose compositum with `U` is `E`, and one `U`-linear embedding of `L` into the
original closure. It realizes `B` as the image of that embedding, obtaining a
finite intermediate field `D₀`. Changing base along the resulting equivalence
and composing with a closure embedding fixing `D₀` identifies the image of `E`
with the actual inertia field of `D₀.asPadicField`. The identification uses
`InertiaNormFieldModels.fieldRange_eq_inertia`, which applies the published
full inertia fixed-field base-change theorem.

`upper_range` proves that the image of the upper generated field is the
supremum of the two images, by induction on field generation. `upper_model`
maps the finite disjoint Galois field into the actual closure, transports
finiteness and Galoisness, and uses the published disjointness-to-ramification
theorem through `total_ramification_of_image_inertia`. The two image equivalences
make the scalar-map square commute on every element.

`actual_models` supplies these hypotheses using `InertiaNormDescent.finite_models`
with empty finite sets and an arbitrary initial unramified stage. The composite
scalar actions are installed from the original two maps. Restricting scalars
makes the lower descended field finite over the original p-adic field. The
lower-model equivalence changes its base presentation; the upper field's
finite dimension, Galoisness and disjointness survive by the rebasing adapters.
The upper-model construction then supplies the stated actual fields and maps.

This implements the finite-model route of Serre, *Local Fields* (1979), V.4,
Lemma 7 and Proposition 7, printed pages 89–90 / PDF pages 96–97, registered
`serre-1979-local-fields`. The explicit closure and scalar-map transports are
derived formalization content. Original and corrections reading details are
in `InertiaNormDescent.md`. No unpublished peer draft was reused.
