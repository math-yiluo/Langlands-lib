# Open charts adapted to the supplied Borel and maximal torus

This internal construction combines `SuppliedTorusAffineChart.exists_over`
with `AffineRegularBorel.adaptedBorelRootBase`. It claims no new theorem from
external literature.

A supplied-torus affine chart expresses the actual pulled-back Borel
inclusion in its model by composing with its ambient comparison inverse.
The relative Borel property is preserved by pullback and that isomorphism.
The coordinate torus inclusion factors through this Borel by the actual
pulled-back supplied torus-to-Borel map and coordinate isomorphism, so its
range is contained on every test scheme.

`SuppliedBorelChart` keeps this affine model, a point in it, and the actual
local Borel-adapted root-base data there. These data include a fixed regular
integer exponent, a root base whose positive roots are exactly the positive
pairings with that exponent, its exact torus-centralizer equality, and an
open neighbourhood on which the dynamic parabolic is the actual supplied
Borel. The final chart scheme is this open neighbourhood; its map to the
original base is etale. It need not be affine.

`SuppliedBorelChart.exists_over` covers each original base point by first
choosing a supplied-torus affine chart and a point above it, and then the
Borel-adapted open chart containing that point. The composite map covers the
original point. No ambient group, supplied torus or supplied Borel is
replaced by an independently chosen one. This pair constructs no adjoint
quotient chart, overlap permutation atlas or Weil presentation yet.
