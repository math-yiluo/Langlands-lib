# Continuous Whittaker evaluation on the smooth real standard module

`RealSmoothWhittakerEvaluationStatement` assumes
`RealSmoothCasselmanWallachExtensionStatement.{0, 0, 0}`. For a uniform real
Whittaker coefficient map \(B\) with irreducible standard source, it gives
a unique continuous complex-linear functional on the genuine smooth
standard representation. Evaluating on actual translates of the original
compact-finite vectors recovers \(B\). The functional satisfies the
Whittaker character identity on every smooth standard vector.

The bounded evaluation reduction supplies existence with agreement on all
translates of the original compact-finite vectors. Their images are dense
in the genuine derivative topology by the compact-finite equivalence and
smooth density theorem. For a fixed unipotent element, the two sides of
the character identity are continuous in the source vector. On the
compact-finite source the identity follows from unipotent covariance of
\(B\) at the group identity. Density extends it to all smooth vectors.
Two continuous evaluations giving the same coefficients agree on the dense
source by evaluation at the identity, which proves uniqueness.

The companion lemma translates the resulting continuous functional to
`IsWhittakerFunctional`, using the finite-word continuity criterion and
the standard character of the scaled real additive character. The
uniqueness in this statement concerns extensions of a fixed coefficient
map \(B\).

This internal reduction supplies a continuous Whittaker functional on
the smooth standard source for comparison with the expanded position
principal series.
