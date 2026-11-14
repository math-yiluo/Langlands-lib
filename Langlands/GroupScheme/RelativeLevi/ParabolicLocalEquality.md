# Local equality of relative parabolics from one residue fibre

This is an internal derived construction from the published proposition
`RelativeParabolicLieContainmentStatement`. It retains that proposition as an
explicit hypothesis and does not prove it.

For two relative parabolic subgroup inclusions in a reductive group over any
scheme, containing a common closed fibrewise maximal relative torus, equality of
their subgroup functors at the residue field of a point implies equality after
restriction to some open neighbourhood of that point, conditional on the
Lie-containment proposition.

The proof applies Lie-containment spreading in both directions. Equality of the
residue-fibre subgroup functors identifies their Lie algebras. Intersecting the
two resulting opens gives the required equality. The helper
`SubgroupFunctor.baseChange_le_of_factorization` proves that subgroup-functor
containment persists under a further restriction, expressing the base change
along the composite map directly. Its proof uses the actual pullback point
equivalence and invariance of membership under isomorphisms of test schemes.

`relativeParabolicLocalEquality` chooses such an open and retains its point
membership and equality of restricted subgroup functors. No Borel conjugacy or
unconditional Lie-containment result is asserted.
