# Finite affine birational models and transport of unirationality

Author: Worker 1630.

This is an internal, derived interface for the actual scheme predicate
`PointTopology.IsUnirational`. The field and all schemes have arbitrary
universe `u`. There is no infinitude, perfection or characteristic
assumption.

`HasFiniteAffineBirationalModel k X` means that, for some finite coordinate
type `ι : Type u`, the structure map of `X` is birational over `Spec k` to
the structure map of the actual affine space `𝔸(ι; Spec k)`. The birational
witness is Mathlib's `Scheme.PartialIso`: an isomorphism between dense open
subschemes, compatible with their maps to `Spec k`. The coordinate type is
explicitly finite. Mathlib's `Scheme.IsRationalOver` does not impose that
restriction, so that predicate alone is not used as a premise here.

`HasFiniteAffineBirationalModel.isUnirational` constructs the morphism
required by the published definition. Given a partial isomorphism from
`X` to affine space, its target is a dense open of affine space, hence
nonempty since affine space over a field is nonempty. The inverse
isomorphism followed by the source open inclusion gives an actual map to
`X`. Compatibility follows from the inverse partial isomorphism's
`IsOver` property. The source inclusion has dense image, and composing it
with an isomorphism preserves dense image. This produces a morphism
over the field from that same finite-dimensional affine open to `X`.

`IsUnirational.map` composes a supplied parametrization with any actual
ground-field morphism having dense underlying image. Its domain,
coordinate type and nonemptiness proof are retained. Density follows
from continuity of the second morphism and the two dense-range
hypotheses. `IsUnirational.of_iso` applies this construction to an
isomorphism over the field, and `isUnirational_iff_of_iso` applies it in
both directions.

The provenance is the published `UnirationalDensity` definition and
Mathlib's `AlgebraicGeometry.Birational.Birational` interface, together
with elementary composition of continuous dense-range maps. No external
structural theorem is asserted. In particular this module does not prove
that a maximal-torus parameter scheme has such a birational model or is
unirational. Those substantive parametrization obligations remain.
