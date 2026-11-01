# Actual Weyl substitution for matrix integrals

This internal derived helper concerns the full-matrix Godement–Jacquet
integrals used in the matrix-to-rank-one comparison. It works directly with
the Library's unsigned long Weyl element and inverse-transpose conventions.
It asserts no matrix or Whittaker functional equation.

For any topological field with continuous ring operations, any absolute value,
and a matrix `A` whose determinant has absolute value one, simultaneous
pullback of the full-matrix Schwartz test and group function by left
multiplication by `A` pulls back the actual matrix integrand. The proof uses
the multiplicativity of `determinantWeight`; the translating weight is one
for every complex parameter.

Every left-invariant Borel group measure is preserved by this translation.
The measurable embedding supplied by the left-multiplication homeomorphism
therefore proves equivalence of absolute convergence and equality of the
totalized Bochner integrals. The integral equality requires no integrability
assumption. The same right half-plane witnesses shifted convergence, and
the identical rational function is a shifted rational value on either side.
The residue parameter, shift, and reduced-denominator continuation condition
are unchanged.

`matrixWeylTranslate` is the pullback of full-matrix Schwartz tests by the
unsigned long Weyl matrix `J`. The identity `inverseTranspose J = J` gives
`dualFunction n f g = coefficientIota f (J * g)`. Applying the actual left
change of variables identifies the integral with test
`matrixWeylTranslate n Φ` and function `dualFunction n f` with the integral
with test `Φ` and function `coefficientIota f`. The same equivalence holds
for convergence, shifted convergence and shifted rational values. The
determinant condition is proved for every real absolute value: `J * J = 1`
implies that the square of its determinant's absolute value is one, and
nonnegativity forces that absolute value to be one.

The final four declarations specialize these results to every canonical
p-adic field and its residue-normalized absolute value and normalized
general-linear Haar measure. They include every natural `n`, so actual matrix
rank is `n + 1`, including rank one. They use the actual unsigned
`dualFunction` and `coefficientIota`, without identifying those functions.

The construction and arguments are derived from the published full-matrix
integral definitions, the actual rectangular Schwartz pullback, determinant
weight multiplicativity, the Library's unsigned Weyl identities, and
Mathlib's measure-preserving change-of-variables theorems. No irreducibility,
smoothness, coefficient-model membership, Fourier normalization or analytic
existence premise is used.

The local canonical topology, valuation, local-field and group measurable
instances use explicit `matrixComparisonWeyl` names. Their mathematical terms
and locality are unchanged. This permits importing the Weyl comparison with
the actual model normalized-generator module without generated-name collisions.
