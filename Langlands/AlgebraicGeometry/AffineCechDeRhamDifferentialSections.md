# Actual affine differential sections over the base ring

On an affine open `W` of a scheme over `Spec R`, `oneFormsSectionsEquiv`
identifies the module of relative Kähler differentials of the section
ring over `R` with the module of sections on `W` of the actual relative
cotangent sheaf. It is linear over the ring of functions of `W` and sends
each algebraic differential of a function to the actual derivation of
that function.

The affine cotangent comparison is initially expressed over the global
functions of `Spec R`. The scalar maps to the ring of functions on `W`
have the same image because the canonical comparison between `R` and
the global functions of `Spec R` is an isomorphism. Kähler differentials
for two scalar maps with equal image are identified through their
universal derivations. The construction composes this identification
with the affine cotangent comparison.

`oneFormsSectionsEquiv_restrict` verifies compatibility under inclusion
of affine opens. The formula on differential generators follows from
naturality of the actual derivation. Extending by linearity with respect
to the same section restriction compares the maps on all one-forms.
This is an internal consequence of `relativeDifferentialsSectionsIso`
and `relativeDifferentialsSectionsIso_inv_D`, applied to the section
algebras of the affine Čech complex.
