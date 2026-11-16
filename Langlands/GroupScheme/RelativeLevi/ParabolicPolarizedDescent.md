# Reduction of parabolic representability to affine polarized descent

This internal reduction applies the explicit proposition
`PolarizedSmoothProperEtaleDescentStatement` to the actual parabolic
presheaf, then uses affine charts and Zariski gluing to reach the unchanged
arbitrary-base `RelativeParabolicSchemeStatement`. Both effective descent
and the local polarizations remain explicit inputs. This file proves
neither of those inputs and claims no unconditional representability result.

For an `AffineEtaleCoverModel c`, `c.Polarization` consists of a
`PresheafLineBundle` on the original parabolic presheaf and ampleness of
its universal bundle on the supplied covering model. The coherent bundle
is assigned to actual families over the original base, including its
cartesian pullback identifications and identity/composition laws. Its
universal bundle is evaluated using the actual restricted representation
of `c.model`, so the represented scheme, smooth proper scheme and ample
bundle all refer to that same local model.

On an affine original base, `exists_descendedModel` applies the supplied
effective-descent theorem to the actual affine etale surjection, big
etale sheafness of the actual parabolic presheaf, its restricted
representation and the supplied polarization. The output is a
`SmoothProperModel` over the original base, together with ampleness of
the universal line bundle from the same coherent data. `descend` chooses
this model and retains the ampleness certificate. The scheme universe is
`u`, and effective descent is instantiated with value universe `u + 1`,
matching the actual parabolic presheaf without a smallness assumption.

`relativeParabolicSchemeStatement_of_affinePolarizedModels` assumes that
for every reductive group over an affine base there is such a covering
model with a polarization. It restricts an arbitrary-base group to each
member of the base's canonical affine open cover, applies the preceding
descent construction and glues the resulting smooth proper models by
`SmoothProperModel.zariskiGlue`. The published equivalence between actual
presheaf representability and the universal-family formulation converts
the resulting model to the unchanged target, including its all-test
uniqueness, smoothness and properness clauses.

The final reduction has no affine or compact restriction on the original
base. It keeps the effective-descent and polarized-local-model hypotheses
explicit. The finite-types proposition can supply an unpolarized covering
model through `affineEtaleCoverModel`; the remaining polarization must be
established separately. All results here are internal compositions of the
imported actual presheaf, sheafness, representing model and descent
interfaces; no new literature translation is claimed.
