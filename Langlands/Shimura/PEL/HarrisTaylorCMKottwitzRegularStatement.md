# Kottwitz's theorem on the Harris CM tower without purity

This module states weight-free forms of the published
`CMHarrisKottwitzTraceComparisonStatement` and `CMHarrisKottwitzLambdaAdicStatement`
(which are unproved statements): Kottwitz's trace identity for the alternating sum of
the cohomology, and the description of the middle degree for a coefficient system of
regular highest weight. It names the vanishing outside the middle degree as an input
and proves that the trace identity and the vanishing give the middle-degree
statement. All declarations are in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel` and use the variables and notations of
the published module `HarrisTaylorCMKottwitzTraceComparison`: the division algebra
data `D`, Harris's charts `C`, the geometric inputs of the tower, the coefficient
field `K`, the algebraic representation `ρ` of the similitude group on `W`, and the
level `U`.

## Definitions

- `CMHarrisKottwitzTraceIdentity d a ι P H`: the polynomials `H i` (`i ≤ 2d`, over `ℂ`)
  are monic, and their alternating characteristic rational function
  `alternatingPolynomial d H = ∏ᵢ H i^{(-1)^i}` equals `ι(P)^a`. This is the published
  `CMHarrisKottwitzVirtualIdentity` without the clause that the roots of `H i` are Weil
  numbers of weight `i + w`. Taking logarithmic derivatives, the identity implies
  `Σᵢ (−1)^i p_m(H i) = a · p_m(ι(P))` for every `m ≥ 1`, where `p_m` is the `m`-th power
  sum of the roots. The converse holds when `P` is monic and all the polynomials have
  nonzero constant terms, as characteristic polynomials of automorphisms (Frobenius on
  the cohomology, and on Kottwitz's `V(π_p, E_v)`) do: then the power sums for all large
  `m` give the identity (the published `alternatingPolynomial_eq_zpow_of_eventual_powerSums`
  in `Langlands/Cohomology/Weights/PowerSums`). Without nonzero constant terms it fails,
  since power sums do not see the root `0`: for `d = 0`, `H 0 = X − 1` and
  `P = X (X − 1)` have the same power sums.
- `CMHarrisKottwitzTraceIdentityStatement` (the trace identity, beside
  `CMHarrisKottwitzTraceComparisonStatement`): under the hypotheses of the published
  statement without the weight `w` and its condition `_hw` (division algebra; `3 ≤ n` or
  a second real place; `ρ` irreducible over `K̄`; `π_f` admissible and irreducible over
  `K̄`), there are `a : ℤ` and a finite set `S` of primes with:
  - for every coefficient place `λ` above `ℓ`, an auxiliary place `v` of `F` above a
    prime `p ≠ ℓ`, polynomials `H` with the published
    `CMHarrisKottwitzFrobeniusComparison` at `v` (unramified cohomology; under the
    fixed-vector comparison, `H i` is the characteristic polynomial of geometric
    Frobenius on the Hecke multiplicity space `W^i(π_f)_λ`), and a monic `P` of positive
    degree with the identity; and in every degree `i > 2(n − 1)`, under the fixed-vector
    comparison in degree `i`, the multiplicity space is zero (`Subsingleton`);
  - at every prime `p₀ ∉ S` with the unramifiedness, chart, level and local-component
    hypotheses of the published statement, three clauses. If `a ≠ 0`, then `π_{p₀}` is
    spherical (Kottwitz's Theorem 1(b)). For every `θ`, square root `s` and Kottwitz
    polynomial `P = P(π_{p₀}, F_v)` (`IsKottwitzPolynomial`), at every coefficient place
    above `ℓ ≠ p₀` the Frobenius comparison at `v = vθ` holds with polynomials `H`
    satisfying the identity with `P`; this is asserted for every `a`, including `a = 0`,
    as in Kottwitz's (5.5) and (5.6). If `π_{p₀}` is not spherical, then for every `θ` and
    every coefficient place above `ℓ ≠ p₀` the Frobenius comparison at `vθ` holds with
    polynomials `H` satisfying the identity with `P = 1`: the virtual representation has
    characteristic rational function `1`, as in (5.6).
- `CMHarrisKottwitzRegularVanishingStatement` (named input): under the same hypotheses
  and regular highest weight of `ρ` (`AlgebraInvolution.IsRegularHighestWeight n ρ`,
  module `Langlands/Shimura/Coefficients/RegularHighestWeight`: in characteristic-zero
  matrix coordinates whose factors are exchanged in pairs by the involution, a highest
  weight vector whose weight is strictly dominant on each `GL_n` factor), for every
  coefficient
  place and every degree `i ≠ n − 1`, the fixed-vector comparison in degree `i` implies
  that the Hecke multiplicity space in degree `i` is zero (`Subsingleton`).
- `CMHarrisKottwitzRegularMiddleDegreeStatement` (the middle degree, beside
  `CMHarrisKottwitzLambdaAdicStatement`): under the same hypotheses with regular highest
  weight, there is `a : ℤ` such that
  - for every coefficient place: the multiplicity spaces vanish in degrees
    `i ≠ n − 1` (under the fixed-vector comparison in degree `i`), and, under the
    fixed-vector comparisons in all degrees, `a ≠ 0` exactly when the multiplicity space
    in degree `n − 1` is nonzero;
  - there is a finite set `S` of primes such that, if `a ≠ 0`, at every prime
    `p₀ ∉ S` with the hypotheses above: `π_{p₀}` is spherical, and for every Kottwitz
    polynomial `P` at `vθ` and every coefficient place above `ℓ ≠ p₀`, under the
    fixed-vector comparisons in all degrees, the continuity hypothesis in degree `n − 1`
    and finiteness (over `K_λ`) of the space of Hecke-linear maps from the fixed vectors
    of `π_f ⊗ K_λ` to the fixed vectors of the cohomology in degree `n − 1`, the
    continuous representation
    `cmHarrisLambdaHeckeMultiplicityObjects` in degree `n − 1` is unramified at `vθ` with
    Euler polynomial the reverse of `P^{|a|}`.
- `CMHarrisKottwitzRegularMiddleDegreeReductionStatement`: the implication trace
  identity → vanishing → middle degree.

## Proved result

`cmHarrisKottwitzRegularMiddleDegree_of_traceIdentity` proves
`CMHarrisKottwitzRegularMiddleDegreeReductionStatement`; only the standard axioms are
used.

The proof takes `a` and `S` from the trace identity. The vanishing clause is the input
itself. At the chart places it uses the sphericity clause under `a ≠ 0` and the clause
for Kottwitz polynomials; the clause for nonspherical components is not needed. For occurrence at a coefficient place, the auxiliary clause gives `H` and a
monic `P` of positive degree with the identity. In every degree `i ≠ n − 1` the
multiplicity space is zero by the input. Its characteristic polynomial, which is `H i`
by the Frobenius comparison, is therefore `1`, since a monic polynomial of degree
`finrank = 0` is `1`. Then `natDegree_pos_iff_of_alternating`
(module `Langlands/Cohomology/Weights/AlternatingConcentration`) shows that `H (n − 1)`
has positive degree exactly when `a ≠ 0`. That degree is the dimension of the
multiplicity space in degree `n − 1`. At the chart places the same argument with
`eq_pow_natAbs_of_alternating` gives `H (n − 1) = P^{|a|}` over `K_λ`, after cancelling the
embedding `j : K_λ → ℂ`. The positivity of the degree of Kottwitz's polynomial is
computed as in the published deduction `cmHarrisKottwitzLambdaAdic_of_traceComparison`
(`hP.monic_and_natDegree` and `kottwitzDim`). The published Euler polynomial transport
`hasEulerPolynomialAt_cmHarrisLambdaHeckeMultiplicityObjects` turns the characteristic
polynomial of Frobenius into the Euler polynomial of the continuous representation. No
weight argument occurs.

## Differences from the published statements

- No weight `w`, no condition on the central scalars, and no Weil-number clauses.
- At the chart places the trace statement asserts the identity with Kottwitz's
  polynomial for every `a`, with `a ≠ 0` guarding only the sphericity, and adds the
  identity with `1` for nonspherical components; the published statement guards the
  whole chart clause by `a ≠ 0`.
- The middle-degree statement assumes regular highest weight of `ρ`. Its conclusion
  concerns degree `n − 1` only, plus the vanishing in the other degrees, where the
  published one factors `P` into pure factors in all degrees.
- At the chart places it assumes the fixed-vector comparison in all degrees, not only
  in degree `n − 1`. The argument needs the vanishing of the other degrees to read the
  middle degree off the alternating identity.

## Sources and the proof of the inputs

R. E. Kottwitz, *On the λ-adic representations associated to some simple Shimura
varieties*, Invent. Math. 108 (1992). Theorem 1, printed p. 657. The remark on regular
highest weight, printed p. 658 (PDF p. 6): by Vogan–Zuckerman, for (essentially)
unitary `π_∞` the cohomology `H^i(𝔤, K_∞; π_∞ ⊗ ξ)` vanishes unless `i = dim S_K`, so
`W^i(π_f)_λ` is trivial unless `i = dim S_K = n − 1`. The trace identity is (5.1)–(5.6),
printed pp. 661–663: (5.5) gives `tr(Φ^j; W(π_f)_λ) = a(π_f) tr(Φ^j; V(π_p, E_v))` for the
virtual representation `W(π_f)_λ = Σ (−1)^i W^i(π_f)_λ`, and (5.6) its characteristic
rational function `P(π_p, E_v)^{a(π_f)}`; when `π_p` is ramified the traces vanish and
the characteristic rational function is `1`. Kottwitz establishes purity at the
beginning of §5 (printed p. 661, by Deligne's theorem) and uses it in §6, printed p. 664,
through (6.1), to exclude cancellation between degrees. The trace calculation
(5.1)–(5.6) itself is independent of the weights. Here regular highest weight excludes
the cancellation instead. Registered `kottwitz-1992-lambda-adic-simple-shimura`, SHA256
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.

D. A. Vogan, Jr. and G. J. Zuckerman, *Unitary representations with non-zero
cohomology*, Compositio Math. 53 (1984), Proposition 5.4 (Matsushima-type comparison),
Theorems 5.5 and 5.6, printed pp. 74–75, stated for connected semisimple groups with
finite centre. Registered `vogan-zuckerman-1984-unitary-nonzero-cohomology`, SHA256
`ccaaf5ad243ccb85d3db629ff7677ca5b80b7e2d71e502d21fa1b773863b78a4`.

A proof of the vanishing input combines these theorems with Matsushima's formula and
the comparison of the `λ`-adic cohomology with the cohomology of the complex points.
Matsushima's formula expresses the cohomology of the compact Shimura varieties through the `(𝔤, K)`-cohomology
of the archimedean components. Kottwitz's group has signature `(n − 1, 1)` at the
distinguished real place and is definite at the others. Removing the positive
similitude factor, the compact factors and the centre `U(1)` of `U(n − 1, 1)` reduces
to `SU(n − 1, 1)`. There Theorem 5.6 gives `A_q(λ)` with `l` a Cartan subalgebra for a
regular highest weight, and Theorem 5.5 gives cohomology only in degree
`R = dim(u ∩ p) = n − 1` (the compact Cartan subalgebra of `SU(n − 1, 1)` gives
`l ∩ p = 0`). Kottwitz computes the trace identity in §5. This module takes both results
as premises of the proved reduction and proves neither.
