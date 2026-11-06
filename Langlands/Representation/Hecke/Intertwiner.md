# Group intertwiners for integrated Hecke actions

This is an internal construction from the existing `Hecke.heckeAction`,
`Hecke.integratedAction_intertwiner`, and `Algebra.LinearIntertwiner`.
For a topological group with its Borel measurable structure, a measure finite
on compact sets and invariant under left multiplication, and two smooth
complex representations, `heckeActionIntertwiner` bundles any original group
intertwiner as a linear intertwiner of their actual measure-indexed Hecke
actions. The group and the three representation carriers have independent
universes. No topology on the carriers is required.

The underlying complex linear map is exactly the original map. Its Hecke
compatibility field is the existing naturality of the finite-fiber integral,
applied to the test function underlying a Hecke algebra element. Both sides use
the same measure and the existing left-Haar convolution convention.

The application and underlying-map formulas hold by definition. Extensionality
proves preservation of identity and composition. Equality of the bundled Hecke
maps implies equality of the original group intertwiners because the underlying
linear maps are unchanged. This only asserts injectivity of this construction;
it supplies no recovery of group equivariance for an arbitrary Hecke map.

The construction does not require a nonzero measure, a compact-open subgroup,
or a normalization choice. It adds no automorphic occurrence, nonvanishing,
admissibility, or existence result.
