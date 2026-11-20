# Convergence and the positive theta Mellin tail

This module develops the Mellin estimates used in the Poisson argument of J. W. Cogdell,
*Analytic theory of L-functions for GL_n* (2004), §2.3, printed pp.208–209. It uses the
Library's idele fundamental domain and the determinant norm of the scalar translate
to write the unfolded kernel.

For a compact set of group points, the log determinant norms are bounded. The
nonnegative-height region therefore imposes a uniform lower bound on the idele log
norm. On this region the real part of the parameter can be replaced by its upper
bound when estimating the exponential weight. Choosing a sufficiently high decay
order in the theta estimate gives an integrable exponential on the resulting real
half-line. The log norm pushes the restricted idele measure forward to Lebesgue
measure. The same estimate gives all real exponential moments for each fixed
group point, so the Library's differentiation theorem gives an entire Mellin tail.

On the negative-height region the idele log norm is bounded above for each group
point. Fixing an admissible theta decay order gives an exponential majorant whose
rate is positive when the real part of the parameter is sufficiently large. The
rate depends on the character, the rank and the field degree. The group point
affects only the constant and the upper endpoint of the half-line. Integrating
this exponential and combining the two regions proves finiteness of the unfolded
majorant on one right half-plane for every group point.

The determinant power of the scalar translate factors into the determinant power
at the group point and the idele power in the section. The first factor is nonzero.
The Library's nonnegative unfolding identity then makes the sum of the section
integrand norm integrals finite. Each term is integrable, and any group point can
be written as one fixed rational coset representative times a group point.
The norm of a section is bounded by its determinant weight times its integrand
norm integral. The determinant weight is invariant under rational translates,
so these bounds give absolute summability. The complex unfolding identity then
identifies the series with the Mellin integral.
