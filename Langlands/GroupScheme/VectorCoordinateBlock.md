# Coordinate blocks over arbitrary rings

Author: Worker 204.

This internal construction extends the coordinate-block maps in
`Rational.VectorCoordinateRealization` from fields to any commutative
base ring. It assumes actual natural additive coordinates on every
scheme test, with no field, reducedness, or connectedness hypothesis.

A finite coordinate block is identified with `Fin m`. Extending by zero
and restricting to those coordinates give natural point homomorphisms,
hence actual group-scheme morphisms by Yoneda. Their composite on the
smaller vector group is the identity, so extension is a monomorphism.
If the ambient scheme is affine over the base, the restriction is
separated. Since the identity factors through extension followed by
restriction, extension is a closed immersion.

The formulas and retraction argument are derived from the existing
field construction, and the proof uses no field-specific step. These
are coordinate geometry helpers; no noncommutative height group or
relative radical is assumed to have additive coordinates.
