# Uniform root expansions for zero-row unequal-rank integrands

`Langlands.RankinSelberg.UnequalRankZeroRowRootExpansionStatement.{uF,uV,uW}
F T n k` is an internal, conditional, pointwise proposition. It uses every
supplied topology `T : F.TopologicalData`, installs its topology, valuation and
local-field instances, and retains independent universes for the field and the
two complex representation spaces. The smaller rank is `n + 1`; the larger
rank is `n + (0 + k + 1) + 1`. Thus every positive gap `k + 1`, including gap
one, is covered. The case `n = 0` is included.

The only mathematical premises are
`CoefficientTorusExpansion (standardCharacter ψ (n + (0 + k + 1))) π` and
`CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ`, for the specified
unitary additive character `ψ`. These premises already provide the full-torus
expansions uniformly for all functionals and all actual coefficient-model
functions. No additional smoothness, admissibility, irreducibility,
Whittaker-type or nonzero condition is imposed here. Hypotheses needed to obtain
the expansion premises belong to the upstream expansion adapter.

In the following formulas, `a` ranges over
`A = Fin (n + 1) → F.Carrierˣ`, indices start at zero, and

```text
d(a)_i = ∏_{j ≥ i} a_j,
K      = Conductor.integralSubgroup
           (ValuativeRel.valuation F.Carrier).integer n,
w(a)   = (∏ i, (T.normalizedAbs(a_i) : ℂ)^((i + 1)(n - i)))⁻¹,
v(a,s) = ∏ j, (T.normalizedAbs(a_j) : ℂ)^((j + 1)s).
```

The powers in `w` are natural powers and the powers in `v` are complex powers.
The formulas for `d`, `K` and `w` are exactly those used in
`QuotientRootIntegrationStatement`; no quotient-integration assertion is a
premise of this statement.

For each pair of representations and character satisfying the two premises,
there exist `m : ℕ` and functions `η_i : A → ℂ`. Each `η_i` is continuous and
has finite-dimensional complex span of all left multiplicative translates
`a ↦ η_i(b * a)`, for every `b : A`. This family is chosen before both
functionals, both coefficients and the compact right translate.

For every `ℓ : glFunctionals ψ (n + (0 + k + 1)) π`,
`ℓ' : glInverseFunctionals ψ n σ`,
`f : (coefficientModel π ℓ).toSubmodule`,
`f' : (coefficientModel σ ℓ').toSubmodule`, and `z : K`, there exist
`Ψ_i : SchwartzBruhat (Fin (n + 1) → F.Carrier)`. They are chosen before `a`
and `s`, and satisfy, for every `a : A` and `s : ℂ`,

```text
unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0
  (Iwasawa.diagonalUnits (d(a)) * z.val) * w(a)
    = ∑ i, Ψ_i((a_j : F.Carrier)_j) * η_i(a) * v(a,s).
```

The second zero is the actual zero matrix in
`Matrix (Fin 0) (Fin (n + 1)) F.Carrier`. The left side uses the published
`unequalRankFunction` itself, with determinant exponent `s - (k + 1)/2`.
The family may be empty; zero functionals, zero coefficients and zero
representation spaces are retained.

## Provenance and derived route

The original source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`. The retained scan has SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Section 2.5, printed pp.388–389, defines finite functions and gives the
full-torus expansion in display (2), with a finite set depending only on the
representation. Printed p.394, display (7), is the diagonal restriction
`W(diag(g,1_(r-t))) W'(g) |det g|^(s-(r-t)/2)`. These original pages were
read visually. No registered JPSS erratum note was found in the checked project
and Library errata locations. The exact conditional interface here is an
internal derived adapter, rather than a verbatim theorem of JPSS.

Here is the intended derivation, which this module states but does not prove.
Right translation by `z` and by its larger-group embedding preserves the
respective actual coefficient models and functionals. Apply the two supplied
expansions to those translated coefficients. Pull back the larger finite
functions along the continuous monoid map
`a ↦ diag(d(a),1_(k+1))` in diagonal-unit coordinates, and the smaller finite
functions along `a ↦ d(a)`. The simple-root coordinates of the larger diagonal
are `(a_0,…,a_n,1,…,1)`, with `k` trailing ones. Restricting its Schwartz factor
to these coordinates supplies compact support in all `n + 1` root variables.
The smaller Schwartz factor uses `(a_0,…,a_(n-1))`. Its pullback alone need not
have compact support in the last variable, but multiplication by the larger
restricted factor gives a Schwartz function in all `n + 1` variables. When
`n = 0`, the smaller factor is a function of the unique empty tuple.

The determinant of `diagonalUnits(d(a))` has normalized absolute value
`∏ j, T.normalizedAbs(a_j)^(j + 1)`. Because `z : K`, its determinant has
normalized absolute value one. Put `β = -((k + 1) : ℂ)/2`. Positivity of the
absolute values of units separates the determinant factor into `v(a,s)` and

```text
c(a) = ∏ j, (T.normalizedAbs(a_j) : ℂ)^((j + 1)β).
```

This fixed factor `c` is a continuous multiplicative character of `A`, hence
has finite-dimensional translation span. For each pair `χ,χ'` of the fixed
finite torus families, take the root-coordinate function
`χ(diag(d(a),1_(k+1))) * χ'(d(a)) * w(a) * c(a)`.
Finite-function closure under products and continuous monoid-map pullback
shows that these functions form the required finite family. The existing
`finiteFunctionClosure` and `rootCoordinateFiniteFunction` helpers describe
these closure operations and the inverse modulus. Reindexing the finite
product by `Fin m` gives the stated quantifier order.

The fixed shift is absorbed into `η`, with no separate spectral-shift premise.
The assertion retains `z : K`; the displayed spectral factor does not assert
the same identity for arbitrary right translates of nonunit determinant.
There is no convergence, rationality, uniform-denominator, Iwasawa,
quotient-measure or Mellin hypothesis or conclusion. Those analytic steps
remain with the parent zero-row analytic proof.
