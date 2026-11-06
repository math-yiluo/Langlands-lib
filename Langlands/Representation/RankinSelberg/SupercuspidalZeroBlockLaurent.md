# Laurent-valued block-zero JPSS integrals for compactly supported Whittaker functions

This internal supporting module shows that the block-zero (`j = 0`) unequal-rank
zeta integral of the published `unequalRankIntegral` is a single Laurent
polynomial in `q^(-s)`, valid for every complex `s`, whenever the restriction
`g ↦ W(diag(g, I))` of the larger Whittaker function is compactly supported
modulo the upper unipotent subgroup `N`. It is the input that the conditional
supercuspidal epsilon-to-gamma assembly (`PadicBlockZeroLaurentValues` in
`SupercuspidalEpsilonGammaReduction`, by Worker 1648) needs. Mathematically this
is the standard observation in Jacquet–Piatetski-Shapiro–Shalika and Henniart
(1993) that for a supercuspidal larger representation the zeta integrals are
Laurent polynomials, so the `L`-factor gives no poles. The Lean statement is
derived here from the Library's determinant-slice expansion and makes no other
claim from the literature.

## Leading blocks

`leadingBlock n d M` is the upper-left `(n+1) × (n+1)` block of a square matrix of
size `n+d+1`. Three multiplicativity facts hold:

- `leadingBlock_mul_appendIdentity`: the block of `M · diag(g, I_d)` is
  `(block of M) · g`;
- `leadingBlock_appendIdentity_mul`: the block of `diag(g, I_d) · M` is
  `g · (block of M)`;
- `leadingBlock_mul_of_upperTriangular`: if `U` is upper triangular then the block
  of `M U` is `(block of M)(block of U)`.

`leadingBlock_one` says the block of the identity is the identity.

## Compact support through `diag(g, I)`

`exists_compact_appendIdentity_support` takes a compact set `C` in `GL_(n+d+1)` and
gives a compact `C'` in `GL_(n+1)` such that `diag(g, I_d) = u c` with `u` upper
unipotent and `c ∈ C` implies `g = v c'` with `v ∈ N_(n+1)` and `c' ∈ C'`. The
proof sets `v` to the leading block of `u`, which is upper unipotent with inverse
the leading block of `u⁻¹` by the triangular rule. The remaining factor
`c' = v⁻¹ g` then has block pair (block of `c`, block of `c⁻¹`). So `C'` is the
preimage under the closed embedding `Units.embedProduct` of the compact image of
`C` under `c ↦ (block of c, op(block of c⁻¹))`. The module also proves privately
that `g ↦ diag(g, I_d)` is continuous, by induction on `d` using
`rankInclusionContinuous`.

`appendIdentity_succ_lastRow` says that `diag(g, I_(d+1))` has last row
`(0, …, 0, 1)`, so it lies in the mirabolic subgroup.

## The Laurent polynomial

The field is a `PadicField` with its canonical topology, valuation and normalized
absolute value. The quotient `N\GL_(n+1)` gets its Borel σ-algebra.
`zeroBlock_residueCardinality_pos` records `0 < q`. `integral_dirac_zeroRows`
evaluates an integral against the point mass on the zero-row matrix space.

`exists_laurent_unequalRankIntegral_zero` takes:

- a Whittaker function `W` on `GL_(n+(0+k+1)+1)` (Lean index `n+(0+k+1)` of
  `WhittakerFunctions`) and an inverse-character Whittaker function `W'` on
  `GL_(n+1)` (Lean index `n` of `InverseWhittakerFunctions`);
- a quotient measure `μ` that is finite on compacts;
- continuity of the block-zero integrand at parameter zero for every `s`;
- the support hypothesis: whenever `W(diag(g, I_(k+1))) ≠ 0`, the matrix
  `diag(g, I_(k+1))` is `u c` with `u` upper unipotent and `c` in a fixed compact
  `C`.

From these it produces Laurent coefficients `L` with
`unequalRankIntegral ψ abv 0 k μ (dirac 0) W W' s = laurentEval (spectralUnit s) L`
for all `s`. The proof goes as follows. The previous lemma gives a compact `K` in
the quotient outside which the integrand vanishes for every `s`. The integrand is
therefore integrable, and the Library's `hasSum_setIntegral_determinantSlice`
expands the integral over determinant slices. The continuous map
`determinantOrder` sends the compact `K` onto a finite set of slice indices, and all
other slices contribute zero. On slice `m`, `unequalRankIntegrand_eq_mul_spectralPoint_zpow`
factors the integrand as its value at `s = 0` times `spectralPoint q s ^ m`. Hence
`L = ∑_m c_m T^m`, where `c_m` is the slice integral at `s = 0`.

## Mirabolic test functions and rational values

`continuous_appendIdentity_of_mirabolicTest` says that for a mirabolic test function
`φ` (`IsMirabolicTestFunction`) the map `g ↦ φ(diag(g, I_(k+1)))` is locally
constant, and so continuous. This uses the open subgroup of the definition's
mirabolic right invariance, pulled back along the continuous map
`h ↦ diag(g⁻¹h, I)`. `exists_compact_appendIdentity_of_mirabolicTest` turns the
definition's compact-support clause, applied to the mirabolic matrix
`diag(g, I_(k+1))`, into the support hypothesis above.

`exists_laurent_of_mem_unequalRankValuesAt_zero` takes
`r = n + (0+k+1)`, a representation `π` of `GL_(r+1)`, a smooth representation
`σ` of `GL_(n+1)`, entrywise functionals `ℓ` and `ℓ'`, and a quotient measure
finite on compacts. It assumes that every vector of the coefficient model of
`(π, ℓ)` is a mirabolic test function. It concludes that every element of
`unequalRankValuesAt 0 k hr q ψ abv μ (rectangularMeasure ν 0 (n+1)) π σ ℓ ℓ'`
is `laurentToRatFunc L` for some Laurent coefficients `L`. The smaller model
function is continuous because `σ` is smooth, and the normalized determinant weight
is continuous. So the integrand on the quotient is continuous, and the previous
theorem gives `L` valid for all `s`. Here `rectangularMeasure ν 0 (n+1)` is the
point mass at zero (`rectangularMeasure_zero_rows`). The image of `L` is a rational
continuation with no excluded points (`laurentToRatFunc_regular_and_eval`), so
uniqueness of rational continuations (`HasRationalContinuation.unique`) identifies it
with the given value.

The conclusion is exactly the clause of the predicate `HasLaurentValues` used by
`PadicBlockZeroLaurentValues`. With the module's canonical local instances, a
compatible quotient measure supplies `IsFiniteMeasureOnCompacts` through
`IsCompatible.regular`.

## Scope

No convergence for arbitrary inputs, existence of rational continuations, functional
equation, `L`-factor statement or supercuspidal Kirillov theorem is asserted. Only
the block `j = 0` is treated. The mirabolic test-function property of the larger
coefficient model is an explicit hypothesis; for an irreducible supercuspidal
representation it follows from the supercuspidal Kirillov statement.
