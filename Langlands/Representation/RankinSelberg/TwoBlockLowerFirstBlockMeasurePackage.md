# Common compatible-measure package for the linked lower mixed quotients

This is derived support for the linked quotient identities of Jacquet,
Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions* (1983),
Section 4.9, equations (2) and (8), printed pages 416 and 418. The registered
source is `jpss-1983-rankin-selberg`. The existence and sigma-finiteness packaging
is an internal measure-theoretic formulation; it is not a quotation of a
separate assertion in the paper.

`MeasurePackageStatement` is the conjunction of the following statements, for
every canonical p-adic field and positive two-block shape.

- `CompatibleExistenceStatement` asserts compatible quotient existence for the
  small full unipotent subgroup in the first block, the mixed subgroup, the
  lower mixed subgroup, and the full ambient unipotent subgroup. All four pairs
  use the specified `generalLinearHaar` and `unipotentHaar`, `mixedHaar`, or
  `lowerMixedHaar`. The latter is the fixed integral-mass-one Haar, chosen
  independently of any rectangular additive Haar.
- `CompatibleFinitenessStatement` asserts sigma-finiteness for every compatible
  choice of all four quotient measures. It also asserts compatibility and
  sigma-finiteness for the lower quotient measure obtained by the exact inverse
  `lowerToStandard` transport, using the inverse-conjugation subgroup measure
  `lowerHaar`.

`compatibleExistence` applies the established closed-subgroup quotient existence
theorems with those fixed measures. `compatibleQuotient_sigmaFinite` supplies
the general finiteness step: a compatible measure is regular; the quotient by
the closed subgroup is Hausdorff, locally compact and second countable; the
standard regular-measure instance therefore gives sigma-finiteness.
`compatibleFiniteness` applies that step to the three first quotients and
uses the established exact lower transport for the ambient unipotent quotient.
`measurePackage` combines these results.

This module does not assert either determinant-slice tower, a density identity,
or the full linked integration proposition. Those conclusions are assembled
using separate kernel and analytic results.
