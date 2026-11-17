# The actual parabolic Lie determinant on quotient components

This internal supporting module compares the exact line bundles in the finite
parabolic determinant ampleness target. It derives the comparisons from the
published coherent determinant pullback isomorphism and the defining restriction
property of the actual glued parabolic family. It asserts no unconditional
positivity result.

`coproductParabolicLieDeterminantDualPullbackIso` works for any index type in the
same universe as the schemes. The actual chosen representative of the glued
family is pulled back along a component inclusion. The canonical determinant
pullback isomorphism identifies its determinant with the determinant of the
actual chosen representative on that component. The actual internal dual
commutes with this pullback, giving the stated isomorphism of line bundles.
`finiteAffineParabolicLieDeterminantDualPullbackIso` specializes this construction
to the actual affine parabolic quotient schemes and their actual universal
conjugate families.

`finiteAffineParabolicLieDeterminantDual_isAmple_iff` proves that the specified
dual determinant is ample on the finite quotient coproduct exactly when the
specified dual determinant is ample on each quotient component. Properness of
the actual coproduct over the affine base gives compactness and
quasi-separatedness. The finite-coproduct ampleness theorem applies to the
actual component pullbacks, and the constructed isomorphisms transport each
component condition. The result makes no nonempty-index assumption.

`finiteAffineParabolicDeterminantDualAmple_of_components` packages the resulting
reduction to single affine parabolic quotients, with the quotient and family
exactly those used in the unchanged target. Its input is genuine ampleness of
each such actual quotient-family determinant dual. Its conclusion is the
existing `FiniteAffineParabolicDeterminantDualAmpleStatement` in every universe.
The empty finite coproduct is included because the local condition is vacuous.

The provenance is the existing actual representative, determinant, dual
pullback, glued-family restriction and finite-coproduct ampleness APIs. These
are formal comparison and assembly results; the geometric positivity required
for a single quotient remains an explicit premise.
