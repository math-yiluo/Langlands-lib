# Actual finite Hecke shell divisor series

Worker 1692 derives this internal analytic support from the actual local
Euler-test formulas in `Langlands.LocalFactor.Abelian.EulerTestShells`, the
prime-ideal convergence and common absolute-value exponent in
`Langlands.Global.Factors.HeckeEulerProduct`, and the general divisor-series
identity in `Langlands.Global.Factors.DivisorEulerProduct`. The results apply to
any number field `K : Type u`, with unrestricted `u`. They do not assume or
prove a global functional equation.

For every finite place `v`, use exactly `CompletionPadic.topologicalData v`, its
canonical `uniformizerUnit`, its residue cardinality and its published
`spectralVariable`. The definition `shellWeight χ v s k` is the local
`shellMellinTerm` of the actual `eulerTest` for `χ.finiteComponent v`. Thus its
normalization is

```
eulerTest χ_v (π_v^k) * (χ_v(π_v) * q_v^(-s))^k.
```

The integer exponent and the local spectral variable are the existing Lean
operations, not newly chosen logarithm branches. `geometricCoefficient` is the
expression inside the last power, before suppressing ramified places.
`shellWeight_zero` proves that the zeroth term is one at every place. At an
unramified place the weight is the geometric term for `k ≥ 0` and zero for
`k < 0`. At a ramified place it is the singleton term one at zero.
`shellWeight_nonzero_norm_le` bounds the norm away from zero by the strictly
positive geometric tail of `geometricCoefficient`.

The helper `hasSum_positive_geometric` sums the nonnegative real family
`if 0 < k then r^k else 0`, over `k : ℤ`, to `r / (1 - r)` for
`0 ≤ r < 1`. The proof shifts the natural geometric series by one and combines
its nonnegative-integer part with its zero negative-integer part.
`summable_positive_geometric` proves joint summability over `ι × ℤ` when
`∑ ‖z i‖` is summable and every `‖z i‖ < 1`. It first sums the positive tail at
each coordinate. Summability of the first coefficients makes them less than
one half outside a finite set; there the tail mass is at most `2 * ‖z i‖`.
Mathlib's nonnegative product-index summability criterion gives the result.
`summable_nonzero_of_eq_off_finset` says that changing finitely many local
series preserves this joint summability away from zero, provided every new
local series is absolutely summable. Its proof uses the same criterion and
cofinite equality of the outer sums.

For the actual Hecke character, the existing common-exponent theorem gives a
real `β` with `‖χ_v(π_v)‖ = N(v)^(-β)` at every finite place.
`norm_geometricCoefficient` proves the exact formula
`‖geometricCoefficient χ v s‖ = N(v)^(-(β + s.re))`, using the published equality
of `q_v` and `N(v)`. Consequently `exists_geometric_convergence` supplies a
right half-plane (`1 - β < s.re`) on which all local geometric coefficients
are strictly contracting and their norms are summable. This uses the existing
prime-ideal norm summability for real exponent greater than one.
`summable_nonzero_shellWeight` combines this estimate with the joint geometric
tail result.

`exists_hasProd_shellWeight` proves on a right half-plane both absolute
summability of the actual divisor coefficients and

```
HasProd (fun v => lFactor T_v χ_v s)
  (∑' d : FinitePlace K →₀ ℤ,
    DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) d).
```

The coefficient is the product over `d.support`, since its exceptional set is
empty. Apply `DivisorEulerProduct.summable_norm_coefficient` and
`DivisorEulerProduct.hasProd_tsum`, then identify each local sum by the actual
`hasSum_eulerTest` theorem. No arithmetic interpretation of the finitely
supported integer functions is used here.

For any supplied local nontrivial unitary additive characters `ψf v` and any
supplied `SelfDualHaar T_v (ψf v)`, `fourierShellWeight χ ψf μ v s k` is the
Mellin term of the actual local Fourier transform of the same `eulerTest`, now
with the inverse local multiplicative character. `hasSum_fourierShellWeight`
is exactly the local identity

```
HasSum (fourierShellWeight χ ψf μ v s)
  (finiteEpsilon χ ψf μ v (1 - s) * lFactor T_v (χ⁻¹)_v s)
```

on its local convergence region. The measure in `finiteEpsilon` is precisely
`(μ v).val.measure`. The argument `1 - s` agrees with the published local shell
identity. Nothing assumes a common choice of the supplied self-dual measures.

At zero multiplicative and additive conductors, every such self-dual Haar gives
the integer ring mass one, by
`HeckeFunctionalEquation.selfDualHaar_integerRing_eq_one`. The existing local
Fourier formula then fixes the unramified Euler test. Its test function equals
the one for the inverse character, since both are the integer-ring indicator.
This proves `fourierShellWeight_eq_shellWeight_inv` for the entire integer-indexed
weight, at every complex `s`.

The remaining Fourier results explicitly assume a finite set `Sψ` outside
which the actual additive conductors vanish. They do not derive this condition
from a global additive character. In
`exists_hasProd_fourierShellWeight`, enlarge `Sψ` by a finite multiplicative
ramification set `Sχ` supplied by the actual Hecke ramification theorem. Outside
`S = Sχ ∪ Sψ`, the Fourier weights equal the inverse-character original weights,
their zeroth terms are one, and every exact finite epsilon is one. On the
inverse character's right half-plane every local Fourier series is absolutely
summable: its unordered local `HasSum` and finite dimensionality of `ℂ` imply
norm summability. Apply the finite-exception stability lemma and the general
divisor identity. This proves absolute summability of the Fourier divisor
series and `HasProd` for the exact family `finiteEpsilon v (1 - s) *
lFactor T_v (χ⁻¹)_v s` with that series as its value.

The Fourier coefficient is the product over `S ∪ d.support`. Every exceptional
zeroth factor remains in the coefficient, including if it vanishes. No
nonvanishing or division by those coefficients is assumed.
`exists_fourierShellWeight_factorization` gives a common right half-plane on
which both the Fourier divisor series and the inverse-character original
series are absolutely summable, and their values satisfy

```
sum_fourier = (∏ v ∈ S, finiteEpsilon χ ψf μ v (1 - s)) * sum_dual.
```

For the implemented proof, the epsilon family has the displayed finite product
as an unordered product because it is one outside `S`. Multiply its `HasProd`
with the inverse character's Euler `HasProd` and use uniqueness against the
Fourier divisor `HasProd`. This comparison uses multiplication only, even at
exceptional zero coefficients.

These are identities of the actual finite local shell weights and their
integer-divisor sums. Arithmetic divisor maps, class-group decompositions,
adelic integral identification, removal of the additive-conductor finiteness
hypothesis, archimedean factors, meromorphic continuation and the final global
functional equation are outside this module's assertions.
