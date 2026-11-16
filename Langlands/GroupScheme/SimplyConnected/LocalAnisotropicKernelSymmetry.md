# Symmetry of the actual anisotropic-kernel Cartan matrix

These are internal consequences of the explicit
`LocalAnisotropicCartanComponentsStatement` premise. This file does not prove
that premise.

A component with actual type-A Cartan entries has symmetric entries. For a
vertex outside the component both entries vanish, by the root-pairing zero
symmetry. Inside it the equality is transported from Mathlib's symmetric
type-A matrix.

`KernelComparison.zero_cartan_symmetric` transports this equality through the
actual anisotropic-kernel vertex equivalence. The local consequence chooses
the actual derived centralizer and its actual Tits index using
`anisotropicKernelIndex`, then applies the component premise. Thus every pair
of ambient zero vertices has equal Cartan entries in both directions.

All field and residue characteristics and the universe are retained. No
unconditional anisotropic classification or rank-one enumeration is claimed.
