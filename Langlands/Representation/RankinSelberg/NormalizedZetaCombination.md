# Finite combinations of normalized rational zeta values

The reciprocal of the normalized L-polynomial belongs to the Laurent span
of the rational zeta values. `IsNormalizedGenerator.reciprocalCombination`
chooses a finitely supported Laurent combination witnessing this membership.
Multiplication by the L-polynomial takes this combination to a combination
of normalized Laurent values equal to one. Evaluation at any nonzero
spectral point preserves the identity.

`exists_bound_laurentEval_spectralUnit` bounds each coefficient of this
identity after evaluation at `q^(-s)` on a closed vertical strip. These
spectral points lie in a compact annulus with positive inner radius. A
Laurent polynomial is the product of a polynomial and a power of the
inverse coordinate, so evaluation is continuous on that annulus. The
same bound applies to normalized local values, which are Laurent
polynomials as well.

The fractional-ideal input comes from Jacquet, Piatetski-Shapiro and
Shalika, *Rankin–Selberg convolutions* (1983), Theorem 2.7(ii), printed
pp. 390–391. The Lean results derive the finite combination and strip
bound from the Library's `IsNormalizedGenerator`, including when it is
applied to the actual ordinary local values via
`normalizedGenerator_ordinaryEqual` and
`normalizedGenerator_ordinaryUnequal`.
