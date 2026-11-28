# Cyclotomic splitting of torsion torus cocycles over number fields

`Langlands.GroupScheme.numberFieldTorusCocycleCyclotomicSplitting` proves
`Langlands.GroupScheme.NumberFieldTorusCocycleCyclotomicSplittingStatement`
in every universe.

The reduction in `NumberFieldTorusCyclotomicSplittingReduction` inflates
the given cocycle from the finite Galois cover to the absolute Galois group.
The tensor description of torus points over the separable closure identifies
the inflated cocycle with one in units–lattice coefficients. The power
condition on the cover gives the annihilation condition for its degree-one
class.

The theorem `numberFieldUnitsLatticeCyclotomicSplitting` gives a positive
level \(N\) whose prime divisors divide \(m\). Its proof uses the local and
global Brauer groups to kill degree-two classes with finite primary
coefficients over prime-power cyclotomic layers, then uses the tensor
Kummer sequence and a uniform degree-one annihilator to obtain the
required coboundary.

The reduction descends its witness to a finite Galois cover over
\(K(\zeta_N)\) and recovers triviality on the pulled-back cover there.
For every extension field \(E/K\) with a primitive \(N\)-th root of
unity, the splitting-field property supplies a \(K\)-embedding
\(K(\zeta_N)\hookrightarrow E\). Pulling back the trivialization along
this embedding proves the conclusion over \(E\).
