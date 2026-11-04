# Lattice indices and full-center quotient volumes

This internal derivation applies the algebraic double-coset index calculus
to finite natural sums in an additive lattice. Induction over the finite
index set combines the power estimate on each ray and the multiplication
estimate. Nonnegative real ray bounds pass through powers and products.
The zero-ray case uses index one at the identity.

For compact open subgroups, all conjugate-intersection indices are finite:
the quotient of a compact subgroup by an open subgroup is finite. A finite
set of translates therefore has a common finite index bound. A smaller
compact open subgroup inside the specified subgroup contributes only its
finite relative index.

The canonical homomorphism to the full-center quotient maps a double coset
onto the double coset of the image subgroup, and the algebraic index calculus
shows that the quotient index cannot increase. The image subgroup is compact
by continuity and open because the quotient map is open. The double coset is
open and measurable. Its exact left-Haar measure is the finite index times
the measure of the image subgroup. That subgroup has finite measure, and
passing through `ENNReal.ofReal` produces a uniform strictly positive real
constant. This argument requires only left Haar invariance.
