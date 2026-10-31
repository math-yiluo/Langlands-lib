# Actual determinant multiplication on the stable automorphic operator core

Author: Worker 2. This internal construction uses the existing actual stable
automorphic functions for every number field `F : Type u` and every natural
rank, including zero, over the complex numbers.

The defining condition of `automorphicOperatorCore` says that every operator
in the concrete generated algebra takes the function into the actual
automorphic form space. For actual finite-order determinant multiplication
`Mχ`, the proved identity
`A Mχ f = Mχ (determinantOperatorConjugationχ(A) f)` reduces this condition
to the original core condition and actual automorphic-form preservation.
The conjugated operator belongs to the same existing algebra. Thus
`mem_automorphicOperatorCore_determinantMultiplier` proves core preservation.

The inverse character preserves the same core and gives every core function
an actual preimage. The resulting image equality defines
`StableAutomorphicFunctions.finiteOrderDeterminantMultiplier` by restriction
of the existing continuous complex-linear equivalence on finite-smooth
functions. It retains the inherited subtype topology.

The whole-algebra covariance formula descends by the faithful subtype
inclusion. The separate finite and standard infinite compact action formulas
have scalar factors `χ(det(ofFinite d))` and `χ(det(ofInfinite k))`,
respectively. The genuine whole enveloping action commutes with the
multiplier. Inclusion into the full automorphic form space agrees with its
multiplier. The forward and inverse pointwise evaluation formulas are actual
determinant multiplication and inverse multiplication.

The provenance is direct internal restriction using
`AutomorphicDeterminantMultiplier`, `DeterminantOperatorConjugation`,
and `OperatorCore`. No original-literature comparison is asserted.
This construction does not identify the stable core with all automorphic
forms or prove it nonzero. Total twists of realized invariant subspaces,
irreducibility, and descent to full operator isomorphism classes remain
subsequent constructions.
