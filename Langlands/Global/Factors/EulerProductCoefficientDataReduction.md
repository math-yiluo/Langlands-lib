# Euler products whose value times a continued coefficient is regular and nonzero

This module is a step toward the published
`Langlands.Global.CuspidalPairBoundaryNonvanishingStatement`.

**Scope.** The module `Langlands.Global.Factors.EulerProductCoefficientDataReduction`
isolates the formal step of Shahidi's proof of Sh81 Thm 5.2. That step passes from a
factorization of a generic Fourier coefficient, together with holomorphy of that
coefficient on the imaginary axis, to the absence of zeros of the partial L-function on
the line `Re s = 1`. The module works with an arbitrary family of Euler factors
`fac : ι → ℂ → ℂ`, with `ι : Type v`. It states and proves:

- `Langlands.Global.EulerProductCoefficientDataReductionStatement.{v}` (the
  statement);
- `Langlands.Global.eulerProductCoefficientDataReduction` (its proof).

It also specializes the result to the partial pair Euler factors of the target
(`EulerProductCoefficientData.enlarged_of_coefficientData`). No analytic input about
automorphic forms is used or proved. The coefficient data are hypotheses here. For
cuspidal pairs they are to be supplied by the statements S1 and S2 of §5.

The module imports only published Library modules:
`Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement` (for
`partialEulerFactor` and `IsPartialPairLFunction`) and
`Langlands.Global.Factors.FiniteComparisonProof` (for the identity-theorem lemma
`FunctionalEquationComparison.eq_on_halfplane_meromorphicEq`). It does not import
the reduction module `Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingReduction`,
and repeats none of its declarations.

## 1. Sources

"p." is the printed page and "PDF" the page of the registered file (printed page =
PDF page + 295).

| Source ID | Short name | Locators used |
|---|---|---|
| `shahidi-1981-certain-l` | Sh81 | §5, Thm 5.1 and its proof, pp.351–352 (PDF 56–57); Thm 5.2 and its proof, p.353 (PDF 58) |

## 2. Definitions

Namespace `Langlands.Global.EulerProductCoefficientData`. Fix `fac : ι → ℂ → ℂ`.

**`IsRepresentative fac L`** says that `L : ℂ → ℂ` is meromorphic at every point
(Mathlib's `Meromorphic`) and that there is a real `σ` such that for every `s` with
`σ < re s`:

- the series `∑_v ‖fac v s - 1‖` converges (`Summable`), and
- the product `∏_v fac v s` converges to `L s` (`HasProd`).

So `L` is a meromorphic continuation of the Euler product of `fac`.

**`CoefficientData fac s₀`**, for a point `s₀ : ℂ`, says that there are functions
`coeff`, `c`, `Ec : ℂ → ℂ` such that:

1. `c` is meromorphic at every point, analytic at `s₀`, and `c s₀ ≠ 0`;
2. `Ec` is meromorphic at every point and analytic at `s₀`;
3. there is a real `σ` such that for every `s` with `σ < re s`, the series
   `∑_v ‖fac v (1 + s) - 1‖` converges, and some `Λ` satisfies
   `HasProd (fun v => fac v (1 + s)) Λ` and `c s = Λ * coeff s`;
4. there is a real `σ'` such that `Ec s = coeff s` whenever `σ' < re s`.

In Sh81's notation, `coeff` is the generic Fourier coefficient of the Eisenstein
series, as a function of the parameter `s`. Clause 3 is the identity
`coeff(s) = c(s) · L^S(1 + s)⁻¹` on a half-plane of absolute convergence, written
without division. `c` is the product of the local Whittaker values at the places in
`S` (Sh81 p.351), which can be chosen nonzero at `s₀`. Clause 4 says that `Ec` is a
meromorphic continuation of `coeff`, and clause 2 that this continuation is
holomorphic at `s₀`.

## 3. Statement

`EulerProductCoefficientDataReductionStatement.{v}` (namespace `Langlands.Global`) is
the proposition: for every `ι : Type v` and every `fac : ι → ℂ → ℂ`, if
`CoefficientData fac s₀` holds at every `s₀` with `re s₀ = 0`, then there is
`L : ℂ → ℂ` with `IsRepresentative fac L` and `meromorphicOrderAt L (1 + y * I) ≤ 0`
for every real `y`.

Order `≤ 0` means that `L` has no zero at `1 + iy`. A pole is not excluded. Order
`⊤`, i.e. `L` identically zero near the point, is excluded, because `⊤ ≤ 0` is
false.

The data may differ from point to point: `coeff`, `c`, `Ec` and the half-planes
depend on `s₀`.

## 4. Proof

The proof follows the argument of Sh81, proof of Thm 5.1, p.352 (PDF 57). A zero of
`L^S` at `1 + s₀` would be a pole of `coeff = c · (L^S)⁻¹` at `s₀`, because
`c(s₀) ≠ 0`. That contradicts the holomorphy of the coefficient at `s₀`. The Lean
proof makes this precise as follows.

- `IsRepresentative.meromorphicOrderAt_eq`: two representatives have the same order
  at every point. On a common half-plane both are values of the same convergent
  product (`HasProd.unique`). The published lemma
  `FunctionalEquationComparison.eq_on_halfplane_meromorphicEq` (identity theorem)
  then makes them agree in a punctured neighbourhood of every point, and
  `meromorphicOrderAt_congr` gives equal orders.
- `eventually_ne_zero_of_data`: from data at `s₀`, `Ec` vanishes identically near no
  point `z`. Suppose `Ec` had order `⊤` at `z`. By the identity theorem on the
  connected set `ℂ`
  (`MeromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected`), it would have order
  `⊤` at a real point `z₁` deep in the half-plane of clauses 3 and 4. There
  `c = Λ · coeff = Λ · Ec`, so `c` would have order `⊤` at `z₁`, and by the identity
  theorem again at `s₀`. But `c` is analytic and nonzero at `s₀`, so its order there
  is `0`.
- `shiftedRepresentative fac c Ec M` (a definition): the function of `s` equal to
  `∏' v, fac v (1 + s)` if `M < re s` and to `c s / Ec s` otherwise.
- `exists_representative_of_data`: data at `s₀` give `c`, `Ec` (analytic at `s₀`,
  `c s₀ ≠ 0`) and a representative `L` with `L (1 + s) = c s / Ec s` in a punctured
  neighbourhood of every point. Take `M = max σ σ'` and
  `G = shiftedRepresentative fac c Ec M`. At every `s` with `Ec s ≠ 0`, `G s` equals
  `c s / Ec s`. For `M < re s` this is clause 3 divided by clause 4. Since `Ec`
  vanishes identically near no point, `G` agrees with the meromorphic function
  `c / Ec` in a punctured neighbourhood of every point. Hence `G` is meromorphic
  (`MeromorphicAt.congr`). Put `L w = G (w - 1)`. It is meromorphic
  (`Meromorphic.meromorphic_fun_comp_sub_const_iff_meromorphic`). On the half-plane
  `1 + M < re w` it is the value of the convergent product of the `fac v w`, by
  clause 3 at `s = w - 1`.
- `exists_representative_order_nonpos` (the derivation core): the data at `s₀ = 0`
  give a representative `L₀`. For real `y`, the data at `s₀ = y * I` give another
  representative `L` with `L (1 + s) = c s / Ec s` near `y * I`. By uniqueness, `L₀`
  and `L` have the same order at `1 + y * I`. That order equals the order of
  `s ↦ L (1 + s)` at `y * I`
  (`meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt`), hence that of
  `c · Ec⁻¹` there (`meromorphicOrderAt_congr`). By `meromorphicOrderAt_mul` and
  `meromorphicOrderAt_inv`, this is `ord c − ord Ec`. The first term is `0`, since
  `c` is analytic and nonzero at `y * I`. The order of `Ec` at `y * I` is finite (by
  `eventually_ne_zero_of_data`) and nonnegative (`Ec` is analytic there). So the
  difference is a nonpositive integer.
- `eulerProductCoefficientDataReduction`: the statement, by
  `exists_representative_order_nonpos`.

### Specialization to partial pair Euler factors

Namespace `Langlands.Global.EulerProductCoefficientData`, with the binders of the
target: `F : Type u` a number field with `[CompactSpace (AdeleQuotient F)]`,
cuspidal realizations `T`, `T'` and spectral presentations
`P : CuspidalSpectralPresentation.{u, uQ} T`, `P'`.

- `isPartialPairLFunction_iff`: for `hP : P.exceptional ⊆ S` and
  `hP' : P'.exceptional ⊆ S`, the published predicate
  `IsPartialPairLFunction P P' hP hP' L` is equivalent to
  `IsRepresentative (partialEulerFactor P P' hP hP') L`. The two differ only in
  `MeromorphicOn L univ` versus `Meromorphic L` (`meromorphicOn_univ`).
- `enlarged_of_coefficientData`: let `S ⊆ S₀`. If `CoefficientData` holds at every
  point of the imaginary axis for the partial Euler factors outside `S₀`, then there
  are `S₀ ⊇ S` and a representative `L₀` of the partial L-function outside `S₀`
  with `meromorphicOrderAt L₀ (1 + y * I) ≤ 0` for every real `y`. This is
  `CuspidalPairBoundaryNonvanishingEnlargedStatement` (the premise of the reduction
  `cuspidalPairBoundaryNonvanishingReduction` in
  `CuspidalPairBoundaryNonvanishingReduction`) for one choice of data and `S`. The
  conclusion is written out rather than citing that premise, so that this module
  does not depend on the reduction module.

## 5. How S1 and S2 supply the coefficient data

The coefficient data come from two statements about the
Eisenstein series on `GL_(r+t+2)` induced from `π ⊗ π'^∨`, with generic coefficient
`coeff ψ φ s`:

- **S1** (`CuspidalPairEisensteinCoefficientStatement`): for every admissible `S`
  and standard additive character `ψ` there is `S₀ ⊇ S` such that for every `s₀` on
  the imaginary axis there are a section `φ` and a function `c`, meromorphic on
  `ℂ`, analytic and nonzero at `s₀`, with clause 3 for
  `fac = partialEulerFactor` outside `S₀` and `coeff = coeff ψ φ`;
- **S2** (`CuspidalPairEisensteinHolomorphyStatement`): for every section `φ`,
  `coeff ψ φ` has a meromorphic continuation `Ec` to `ℂ`, analytic at every `y * I`.

For each `s₀ = (im s₀) * I` on the imaginary axis, S1 gives `φ` and `c`, and S2
applied to that `φ` gives `Ec`. Together they give `CoefficientData` at `s₀`.
`enlarged_of_coefficientData` then gives the premise of the reduction
`cuspidalPairBoundaryNonvanishingReduction`, and that reduction gives the target. The
derivation of the premise from S1 and S2 is the separate module
`Langlands.Global.Factors.CuspidalPairEisensteinDerivation`
(`cuspidalPairBoundaryNonvanishingEnlarged_of_eisenstein`). Neither S1 nor S2 is
stated or proved here.

## 6. Provenance

- The statement is derived from Sh81, proof of Thm 5.1 (pp.351–352). There
  Shahidi concludes from the factorization of the generic Fourier coefficient and
  from the holomorphy of the Eisenstein series on the imaginary axis that the
  partial L-function has no zero at `1 + a_1 s₀`. Here the argument is abstracted
  to an arbitrary family of Euler factors, and stated with one unit of shift
  (`a_1 = 1`). The rescaling `s ↦ (n + m) s` of Sh81 is absorbed in the
  parametrization of the Eisenstein series in S1.
- The formalization is internal: the construction of the continuation `c / Ec`,
  with its correction on the half-plane of convergence, and the order computation
  are written for this module. The uniqueness argument repeats, for
  `IsRepresentative`, the one that `CuspidalPairBoundaryNonvanishingReduction` proves
  for `IsPartialPairLFunction`.

## 7. What is not proved

- The coefficient data for cuspidal pairs, i.e. statements S1 and S2, are neither
  stated nor proved here. Hence neither the premise
  `CuspidalPairBoundaryNonvanishingEnlargedStatement` nor the target
  `CuspidalPairBoundaryNonvanishingStatement` is proved by this module.
- Nothing is claimed about poles on `Re s = 1` or about zeros off that line.
