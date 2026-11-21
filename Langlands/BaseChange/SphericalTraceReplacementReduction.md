# Algebraic replacement of regular elementary traces by spherical traces

`sphericalTraceReplacementReduction` proves
`SphericalTraceReplacementReductionStatement`. It takes two finite families
with regular elementary traces, spherical traces, and complex weights. Each
family has a label and a predicate selecting its spherical contributors. The
same finite type labels both families. Each label has a selected character and
a positive natural multiplicity.

The premises specify the local trace data.

- `HasElementaryTraceExpansion` expresses the elementary trace of each
  contributor as its finite character sum times a scalar. The scalar is common
  to both families and nonzero at every strictly decreasing integer weight.
  `JacquetWeightMultiplicities` gives the natural counts of characters of the
  valuation lattice. The base-field expansion uses the characters after
  pullback by the norm, with counts taken after pullback.
- `DetectsSphericalContributors` gives the coefficient of the selected
  character at each label. The coefficient is the label's prescribed count for
  each spherical contributor with that label, and zero in all other cases.
- `HasSphericalTraceValues` expresses the spherical trace on each test as the
  common value for the contributor's label if the contributor is spherical, and
  zero otherwise. The base-field spherical trace uses the image under the
  base-change homomorphism.

Given equality of the weighted elementary traces on all strict weights, the
proof uses `strictWeightCharacterCoefficients_eq` to identify the two weighted
finitely supported families of character coefficients. At each selected
character, the coefficient equality becomes an equality of sums of the
weights of the spherical contributors at its label, multiplied by the same
nonzero count. Cancellation gives equality of the weight sums. Multiplying
each such sum by the corresponding common spherical trace value and summing
over the finite label type proves the replacement identity for every test.

This is the algebraic part of the separation argument in Henniart–Lemaire,
*Changement de base et induction automorphe pour* `GL_n` *en caractéristique
non nulle*, I.5.5, printed pp. 37–39 (PDF pp. 45–47). In that application the
labels are Satake parameters on the extension side, with powered parameters on
the base side. The Jacquet expansion of the regular elementary traces comes
from I.5.3 and I.5.4. The use of the opposite Weyl characters in I.5.5 motivates
the selected coefficients, and Lemma 2 of I.5.5 gives the spherical evaluation
for the unramified induction. The local expansion, selected coefficient
multiplicities, and common spherical evaluation enter the Lean theorem as
explicit premises.
