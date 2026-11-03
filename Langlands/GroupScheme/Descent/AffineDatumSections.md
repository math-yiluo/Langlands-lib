# Compatible sections of an affine descent solution

This is an internal categorical adapter for an actual Čech datum
`D : Descent.Datum p G` and a supplied underlying solution
`s : AffineSchemeSolution D`. All schemes and test schemes are in arbitrary
universe `u`. No field, smoothness, finite type or commutativity assumption
is made.

The construction is derived from the full kernel pair in `AffineDatumScheme`,
the multiplicative transport in `SectionTransport`, and Mathlib's fpqc effective
epimorphisms. It asserts no new original-literature result.

## Transport and the quotient

`AffineSchemeSolution.move_proj` proves that a point and its transported point
have equal images in the quotient. For every test scheme `Z`, two maps from
`Z` to `G` lying over specified maps `z₁,z₂ : Z ⟶ S` with the same image in `B`
are related by `D.sectionTransport` exactly when their quotient images agree.
The reverse direction of `sectionTransport_eq_iff` uses the actual kernel-pair
lift and `Datum.move_relation`. These facts require no geometric hypothesis
on `p` beyond the supplied underlying solution.

`AffineSchemeSolution.sectionSubgroup (D := D) U` is a subgroup of the group
of sections from `p*U` to `G`. A section belongs to it when, for every test
scheme `Z` and every two maps `a,b : Z ⟶ p*U` with the same projection to `U`,
transport carries its value at `a` to its value at `b`. The subgroup depends
only on `D` and `U`, not on a chosen solution. Precomposition preserves the
section group operations, and `D.sectionTransport` is multiplicative, so
compatible sections are closed under the identity, product and inverse.

## Represented compatible sections

`localSection f` restricts a section `f : U ⟶ s.obj` by actual slice pullback
and then applies `s.iso.hom`. Its composite with `s.proj` is the projection
to `U` followed by `f.left`. Hence it is compatible. These formulas also
require no geometric hypothesis on `p`.

Under `[Flat p] [Surjective p] [QuasiCompact p]`, `localSection_injective`
follows from faithful fpqc pullback. Conversely, compatibility says exactly
that a local section followed by `s.proj` agrees on every pair above equal
points of `U`. The fpqc projection `p*U ⟶ U` is an effective epimorphism, so
`sectionDesc` descends this map. Epimorphism cancellation verifies that it is
over `B`; the supplied pullback square verifies recovery of the original
local section. The resulting equivalence is

```lean
s.sectionEquiv U : (U ⟶ s.obj) ≃ sectionSubgroup (D := D) U
```

Its inverse is the constructed descent, not assumed representability.
Although a supplied `AffineSchemeSolution` has an affine underlying scheme,
this section argument imposes no additional affineness condition on `B`, `S`
or `U`.

This module stops at the section equivalence. Reconstruction of the quotient's
group object, its group-compatible pullback isomorphism, object effectivity
and simply connected cover existence remain further obligations.
