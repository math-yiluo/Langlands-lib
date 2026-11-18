# The real-place functional equation from local equations on a uniform coefficient space

This internal reduction introduces two new local analytic premises on the refined
`realUniformWhittakerModel`, proves actual global restrictions belong to that space,
and reduces the unchanged `RealPlaceFunctionalEquationStatement.{u}` to those two
premises and `RealPlaceContragredientPairLStatement.{u}`. These three premises remain
open. The earlier coefficient space and every reviewed statement using it are unchanged.
This is an intermediate result, not the unconditional functional equation.

`RealLocalUniformUnequalJacquetStatement` quantifies rank indices `t < r`, real block
lists of total ranks `r+1` and `t+1`, a nonzero real additive parameter `a`, every
compatible real quotient measure, and functions in the refined coefficient models for
`a` and `-a`. It requires the full existing `RealJacquet.UnequalEquation` package:
integrability in a right half-plane, holomorphy there, meromorphic continuations with
half-plane agreement, and the multiplied-out local functional equation with the actual
dual integrals. The dual block lists apply `RealLocalJacquet.dualBlock` to the original
lists; epsilon uses `-a` with the prescribed positive self-dual scale. The source sign
is `determinant(ds,-1)^(t+1) * determinant(es,-1)`.

`RealLocalUniformPositiveEqualJacquetStatement` uses the same refined models in equal
ranks with `0 < r`, every compatible quotient measure and every Schwartz function.
It requires `RealJacquet.EqualEquation` with additive parameters `a` and `-a`, the same
dual block lists, and source sign `determinant(ds,-1)^r`. The rank-index-zero case is
supplied separately by the existing unconditional real Tate argument in the final
analytic adapter.

The refined space imposes a common growth exponent before all source vectors of each
generating coefficient map. Its proved regularity consequently supplies one exponent
for every derivative word of any of its members. This removes the previously identified
missing uniform bound from the hypotheses available for a convergence argument.
It does not itself prove either new local analytic premise. Their continuation,
functional equation, and any continuous-model and measure-normalization comparisons
needed to establish their full stated scope remain proof obligations.

`RealPlaceUniformWhittakerModelStatement.{u}` has the same actual global data and two
character branches as the earlier model-membership statement. The theorem
`realPlaceUniformWhittakerModel` proves it. For each genuine real-place standard-module
map `A`, the existing analytic bridge constructs the coefficient map
`B f(g) = cuspWhittaker F T χ (A f) (realPlacePoint F (r+1) w g * finitePoint F (r+1) b)`
and proves all five original intertwiner conditions. The proved global real-slice
growth bound chooses its exponent before every vector of the cuspidal realization.
Applying it to `A f` therefore proves the extra uniform condition for `B`, without
assuming uniform growth for arbitrary automorphic forms or arbitrary older-model maps.

Supremum induction over the place-isotypic subspace proves membership of each actual
restriction: generating ranges use these uniform intertwiners, zero uses coefficient
linearity, and sums use additivity. The existing irreducibility and nontrivial-standard-
module result identify the actual place-isotypic subspace with the entire realization.
The standard-character and real-component lemmas supply both the original unitary
adelic character and its inverse, with real parameters `a` and `-a`.

`RealPlaceUniformLocalTheoryReductionStatement.{u}` retains exactly the two new uniform
local analytic premises and the existing actual dual-denominator comparison. Its proof
uses the proved refined membership to apply the local packages, rewrites the entire
dual denominator with the third premise, and rewrites the parameter signs using the
proved actual minus-one scalar comparison. The existing positive-rank convention
adapter then yields the exact full target, including its rank-index-zero branch and
free number-field universe.

Provenance is internal. This follows the already implemented local-to-global
restriction reduction with a separately defined smaller coefficient space. Actual
membership is supplied from the unconditional Whittaker regularity and common-vector
growth proof; the three retained premises are neither assumed implicitly nor claimed
as proved.
