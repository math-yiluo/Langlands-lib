# Actual Lie kernels and cotangents in an explicit corepresentation

This internal construction adapts `Lie.AffineCoordinates` and
`Lie.SmoothFiniteProjective` to an explicitly supplied corepresenting algebra.
It uses the same actual affine test points and dual-number kernel.
No new external literature assertion is used.

The explicit algebra maps classify actual points and commute with coefficient
maps. The actual identity point is classified by the corepresentation counit.
Thus an actual kernel point is an algebra lift of the specified augmentation
to dual numbers, or equivalently an augmentation derivation.
Epsilon scaling is scalar multiplication. A square-zero extension with two
independent infinitesimal directions shows that kernel multiplication
corresponds to addition of derivations.

The universal property of Kähler differentials and scalar extension identifies
these derivations with the dual of the actual augmentation cotangent in the
explicit algebra. For a smooth algebra the augmentation cotangent is finite
projective, hence reflexive. Dualizing a supplied free-line Lie equivalence
therefore trivializes this cotangent.

The derivation comparison allows any coefficient algebra with a supplied
action of the corepresenting algebra and scalar tower, provided that action's
algebra map equals the actual counit followed by the coefficient map.
The cotangent statements specialize the coefficients to the base ring.
The final freeness construction assumes smoothness of the explicit algebra
over the base ring. All statements retain an arbitrary commutative base in
universe u, without field, localness, reducedness, connectedness or
nontriviality assumptions.

This explicit-presentation comparison supplies a bridge for the dynamic
root-coordinate construction. It does not itself assert that the required
Lie-line equivalence or graded coordinate exists.
