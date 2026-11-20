# Linearizing a scalar on finite jets

This auxiliary module derives equivariant polynomial equations from the
strict scalar action of the formal modules. Suppose the residue of a scalar
\(a\) in the coefficient field is \(c\), with \(c^m=1\) and \(m\) invertible
in the field. At a fixed characteristic-power width, assume \(a^m\) fixes
the tautological points of both formal modules.

On each jet, average the pullbacks of a coordinate under the iterates of
\(a\), weighting the \(j\)-th iterate by \(c^{-j}/m\). The averaged coordinate
agrees with the original modulo the square of the augmentation ideal because
the linear scalar action is \(c\). Substitution by the averaged coordinates
induces the identity on each graded piece of the augmentation filtration.
It is injective by nilpotence of the filtration and hence bijective by finite
dimensionality. Shifting the averaging sum shows that the scalar acts by \(c\)
on the new coordinates. These substitutions are compatible with jet
restriction.

In the new source and target coordinates the pullback of the formal
homomorphism commutes with diagonal scaling, since the original map was
scalar-linear. Its target coordinate images have weight \(c\) in the
source jet. Averaging polynomial lifts under diagonal scaling gives
polynomial equations of the same weight. `exists_equivariant_equations`
compares the resulting quotient dimension with the original kernel quotient
dimension at the chosen width and at every smaller characteristic-power
width greater than one.
