# Coordinate changes between glued projective schemes

Fix a locally directed open cover of a scheme and two strict invertible
coordinate cocycles of the same finite rank on that cover.
`CoordinateCocycle.Change d e` consists of an invertible matrix of global
functions on each cover member. Its compatibility equation says that
changing coordinates and then applying the second transition agrees
with applying the first transition and then the restricted coordinate
change on the target chart.

`Change.naturalIso` constructs the actual natural isomorphism of the
projective chart diagrams. The proof uses naturality of the global
linear action, including pullback of all its coefficients, and the
specified compatibility equation.

When the index category is thin and small in the scheme universe, the
two chart diagrams have the scheme colimits constructed in
`CocycleGluing`. Applying the colimit map to the natural isomorphism
constructs `Change.schemeIso`. Its forward and inverse chart equations
are the stated projective actions. Both morphisms commute with the
structure maps to the original base. The forward chart equation
determines the comparison morphism uniquely.

This is derived internal infrastructure. It uses the previously
constructed relative projective actions and their coefficient
naturality, and Mathlib's natural isomorphisms and colimit universal
property. It uses no new external source assertion. The cover, the two
cocycles and their compatible change are input. This file does not yet
construct a change from sheaf frames, a line-bundle twist comparison,
or a representing ordinary moduli scheme.
