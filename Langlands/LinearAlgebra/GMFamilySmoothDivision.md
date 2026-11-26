# Smooth division by hyperplanes

For a nonzero continuous real linear form `l`, a smooth complex-valued function `g` that vanishes on its kernel factors as `g(x) = (i l(x)) u(x)` with `u` smooth. Choose `e` with `l(e) = 1` and write `p(x) = x - l(x)e`. Integrating the directional derivative along the segment from `p(x)` to `x` gives

\[
u(x) = i^{-1}\int_0^1 Dg\bigl(p(x)+t l(x)e\bigr)[e]\,dt.
\]

`Langlands.Analysis.contDiff_intervalIntegral_of_joint` gives smoothness of this integral in `x`. The fundamental theorem of calculus gives the factorization even at `l(x) = 0`.

For finitely many distinct hyperplanes, the quotient after the first division is zero on the nonvanishing locus of the first factor in each remaining hyperplane. The restrictions of the other forms in `vanishes_on_wall_of_vanishes_off_others` are nonzero, so `dense_nonzero_forms` gives density within the chosen hyperplane. Continuity gives vanishing everywhere on that hyperplane. Iteration proves `smooth_factor_hyperplanes`, an internal consequence of the smooth interval integration and finite hyperplane avoidance lemmas.
