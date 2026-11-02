# Mapping properties on actual affine scheme points

Author: Worker 105.

These targets express the affine scheme-morphism assertions of Brian
Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 2.1 and its proof, printed pages 2–3.
Registered source `conrad-2011-weil-grothendieck-adelic-points`,
SHA256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

For actual affine schemes `X` and `Y` over `Spec R`, and a commutative
`R`-algebra `S` equipped with a topology,
`AffineSchemeContinuityProperty` asserts that postcomposition with every
scheme morphism over the base is continuous on the actual relative
point sets `RingPoint`. Their topologies are those constructed from
global-section evaluation in `AffineScheme`.

`AffineSchemeClosedImmersionProperties` asserts that postcomposition
with a closed immersion is an embedding. If `S` is Hausdorff, it is a
closed embedding. `AffineSchemeMapProperties` combines these targets.
The closedness clause retains its own Hausdorff hypothesis.

This is a derived extension of the affine mapping part of the source:
the value ring may be a separate `R`-algebra `S`; finite type and
continuous ring operations are unnecessary for these particular
mapping assertions. The algebraic reason is that precomposition of
coordinate algebra maps is continuous for evaluation topologies, and
a closed immersion of affine schemes induces a surjective map on
global sections. Only `S` has a topology. Setting `S = R` recovers
these assertions in the source's affine setting.

These targets do not assert nonaffine gluing, products, local
compactness, finite-coordinate presentations or axiomatic uniqueness.
