# Generic paths and specialization of regular crossing maps

This module derives path and specialization helpers from the explicit
shifted crossing maps and the weak analytic calculus. It uses no new analytic
continuation assumption or outside source.

`HasGenericPath d e` means that a nontrivial filter approaches zero through
nonzero shifts where all four scalar parameters are generic. A parameter with
nonzero imaginary part avoids every real exceptional root. The four shifted
parameters have the same imaginary part as `d.exponent - e.exponent + z`.
Consequently, when the central exponents have equal imaginary parts, the image
of the positive real neighborhood filter under `r ↦ r I` is a generic path.
Continuity gives convergence to zero, and the positive real filter is
nontrivial.

For valid admissible choices and any such nontrivial generic approaching
filter, the inclusion of the target-valued regular family at zero equals its
ambient regular value. Both ambient families are weakly analytic at zero,
agree on the generic path, and hence have the same central value by scalar
continuity and algebraic dual separation. This also proves that the ambient
regular value belongs to the actual target induction module.

The same specialization argument proves compact equivariance at zero. For a
fixed compact element and source vector, both sides are weakly analytic
families; generic shifted maps commute with the compact action.

Validity and admissibility remain hypotheses. This module does not construct
the arithmetic choices or prove limiting Lie intertwining, so it alone does
not prove the full induced swap statement.
