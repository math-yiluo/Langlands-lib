# Smoothness and growth of actual real-place Whittaker restrictions

This internal module specializes the place-independent Whittaker regularity proof of
Worker 5665 to a real place. It proves `RealPlaceWhittakerSmoothGrowthStatement`,
`RealPlaceWhittakerAnalyticStatement`, and `RealPlaceWhittakerModelStatement` without
additional premises, and states and proves a conditional reduction of the full real-place
functional equation to its two local analytic packages and its actual contragredient
denominator comparison. These three inputs remain open; the unconditional functional
equation is not proved here.

For a number field `F` with compact adele quotient, an actual cuspidal realization `T` of
`GL_(r+1)`, a standard adelic additive character `χ`, a real place `w`, and a fixed finite
adelic component `b`, write

`W_x(g) = cuspWhittaker F T χ x (realPlacePoint F (r+1) w g * finitePoint F (r+1) b)`.

The real-place insertion `realPlaceMatrix w A` places `A` at `w` and identities at all
other infinite places. Its linear part `realDirection w` places its argument at `w`
and zeros elsewhere. The coordinate calculations prove that insertion is affine and
smooth, agrees with the matrix of `realPlaceGL`, and preserves invertibility.
`realPlacePoint_mul_finitePoint` identifies the actual adelic point with
`adelicPoint F (r+1) (realPlaceGL F (r+1) w g) b`.

The shared `ArchimedeanWhittakerRegularity.archWhittakerExt` equals the genuine Whittaker
coefficient at invertible matrices. Composing its smoothness on the open set of invertible
archimedean matrices with real-place insertion gives a smooth extension of `W_x` to the
open set of invertible real matrices. `Archimedean.contMDiff_of_contDiffOn` gives the
matrix-manifold smoothness required by the statement.

The growth argument preserves the quantifier order in the shared global theorem:
there is a single real exponent `β` for the entire realization, before choosing a standard
character or vector. The real-slice determinant theorem bounds `detNorm^β` by `D H(g)^N`
for `D ≥ 0` and `N : ℕ`, where `H = realMatrixHeight` is the sum of the squared entries of
the matrix and its inverse. These choices precede the vector and character. Multiplying
the global coefficient constant by `D` proves
`exists_uniform_norm_cuspWhittaker_realPlace_le`: one `N` works for every vector and every
standard character of this realization on this fixed slice, with nonnegative constants
allowed to depend on the vector and character.

These two arguments prove `realPlaceWhittakerSmoothGrowth`. The previously proved
`realPlaceWhittakerAnalytic_of_smoothGrowth` supplies genuine Lie compatibility by comparing
two derivatives of the same actual Whittaker curve. The existing algebraic bridge then
proves membership of actual restrictions in the specified local coefficient model.

`RealPlaceFunctionalEquationLocalReductionStatement.{u}` retains precisely
`RealLocalUnequalJacquetStatement`, `RealLocalPositiveEqualJacquetStatement`, and
`RealPlaceContragredientPairLStatement.{u}`. Its consequent is exactly the unchanged
`RealPlaceFunctionalEquationStatement.{u}`. Its proof supplies the now proved smoothness
and growth to the earlier four-input reduction. It retains the free number-field universe
and both rank cases, including rank index zero.

Provenance is internal: the shared core differentiates the genuine Whittaker integral
using the realization's enveloping action, finite measure on a unipotent fundamental
domain, and determinant-band bounds, and proves its global growth bound from
`CuspCentralBound.exists_norm_cuspFunction_le`. The real-place proof uses that core,
elementary affine coordinate insertion, the previously proved actual determinant
normalization, and the existing algebraic bridge. It asserts no globalization or uniform
growth theorem for arbitrary members of the internal local coefficient space.
