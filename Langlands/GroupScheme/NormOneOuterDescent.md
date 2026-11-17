# Opposite algebras from equivariant outer norm-one matrix formulas

This internal algebraic helper works with a finite-dimensional central simple
algebra and a splitting-field matrix chart. The chart identifies its actual
reduced-norm-one tensor units with the full determinant-one matrix group.
Consequently these units span the scalar-extended algebra: the proof transports
the published matrix-span theorem, which covers all sizes and characteristics.

Suppose an automorphism of the norm-one tensor group is covariant for coefficient
Galois conjugation, and in the chosen chart acts as conjugated inverse transpose.
Conjugated transpose itself defines an algebra anti-equivalence. On norm-one
elements it equals the supplied group automorphism composed with inversion.
The covariance assumption therefore makes this anti-equivalence equivariant
on norm-one elements. Span induction, using additivity and the semilinearity
of coefficient conjugation, extends equivariance to the whole scalar-extended
algebra.

For a finite Galois splitting field the noncommutative fixed-tensor descent
construction then gives a scalar-fixing algebra equivalence from the original
algebra to its opposite. No involutivity is asserted.

The provenance is internal. This module implements the algebraic outer-case
descent step for `NormOneCenterAutomorphismOppositeStatement`. It retains a
supplied outer matrix formula and Galois covariance as explicit hypotheses.
Proving that a centre-moving actual group-scheme automorphism supplies those
hypotheses is a separate step; this module does not assert that classification.
