# The middle-degree family supplied by Kottwitz's theorem

`HarrisKottwitzMiddleDegreeStatement` is a reduction to the published
`CMHarrisKottwitzLambdaAdicStatement` (Kottwitz 1992, Theorem 1, p. 657). It is
stated at the same actual arguments: the CM datum `D`, Harris signature charts
`C`, the PEL inputs, the representability input `q`, the coefficient
representation `ρ` over the number field `K`, the dual-scheme inputs, rigidity
and one small level `U`. It turns Kottwitz's conclusion into the form needed by
`HarrisPowerSystem`: one exponent, one finite set of places and one family of
`K`-rational polynomials.

## Premises

Besides Kottwitz's own hypotheses on `A`, `ρ`, the central weight `w` and an
admissible representation `πf` over `K` that is irreducible over `K̄`, there are
three premises. All of them concern the same `πf ⊗_K K_λ` and the same tower
objects that appear in Kottwitz's statement.

1. **Concentration.** At every coefficient place `λ` of `K` where the actual
   fixed-vector comparisons `CMHarrisLambdaTowerFixedVectorComparison` hold in
   all degrees, the Hecke multiplicity space
   `cmHarrisLambdaTowerHeckeMultiplicity` at level `U` vanishes in every degree
   `i ≠ n - 1`.
2. **Occurrence.** At one coefficient place `λ₀` of `K`, the actual
   fixed-vector comparisons hold in all degrees, the level cohomology is
   continuous in every degree (`CMHarrisLambdaCohomologyContinuous` at `U`),
   and the degree-`n - 1` Hecke multiplicity space at level `U` is nonzero.
   The continuity is what lets Kottwitz's Euler clause be applied at `λ₀` in
   the degrees `i ≠ n - 1`.
3. **Good primes.** Outside a finite set of rational primes `p₀`,
   `HarrisKottwitzGoodPrime` holds. `F` is unramified at `p₀`, and an
   unramified chart `c` has the `p₀`-component of `U` as its level, in exactly
   the product form of Kottwitz's statement. Also, `πf` is the actual tensor
   product of a `p₀`-component `πp` and a prime-to-`p₀` representation. For
   every `θ : ℂ → Q̄_{p₀}`, `πp` has a Kottwitz polynomial `P(πp, F_v)` with
   coefficients in `K` (`IsKottwitzPolynomial`, with Harris's Hodge function).

## Conclusion

There are an integer `a ≠ 0`, a finite set `S` of finite places of `F` and
polynomials `Q v ∈ K[X]` with the following properties.

- For `v ∉ S`, `Q v` is monic and pure of weight `(n - 1) + w` for
  `q = N(v)` (`IsPurePolynomial`).
- For `v ∉ S` there are a prime `p₀`, a chart `c`, a component `πp` of `πf`, an
  embedding `θ` with `vθ = v` and a square root `s` of `p₀`. For these,
  `πp` is spherical irreducible for `c`, and `Q v` is its Kottwitz polynomial.
  This is the hook for the later spherical comparison with the source.
- At every coefficient place `λ` take the actual fixed-vector comparisons and
  continuity in all degrees, and finite-dimensionality of the degree-`n - 1`
  Hecke multiplicity space. Then `cmHarrisLambdaHeckeMultiplicityObjects` in
  degree `n - 1` has, at every `v ∉ S` of residue characteristic different
  from that of `λ`, Euler polynomial `reverse((Q v)^{|a|})` over `K_λ`.

## Expected proof

Kottwitz's part (a) at the occurrence place `λ₀` gives `a ≠ 0`. Let `ℓ₀` be
the rational prime below `λ₀`. Take `S` to be the places of `F` above
Kottwitz's exceptional primes, above the primes excluded in premise 3, and
above `ℓ₀`. Given `v ∉ S` above `p₀`, choose `θ` with `vθ = v` and take `Q v`
to be the `K`-rational Kottwitz polynomial `P` of premise 3. Part (b) gives the
unique factorization `P = ∏ P_i` into pure factors of weight `i + w`. Since
`p₀ ≠ ℓ₀`, part (b) applies at `λ₀` in every degree `i ≤ 2(n - 1)`, using the
comparisons and continuity of premise 2. For `i ≠ n - 1` the Hecke
multiplicity space at `λ₀` is zero by premise 1. It is therefore finite, and
its Euler polynomial is `1`, so `reverse(P_i^{|a|}) = 1` over `K_{λ₀}`. A pure
polynomial is monic and its complex roots are Weil numbers, hence nonzero.
Since `|a| > 0`, this forces `P_i = 1`. Therefore `P = P_{n-1}`, which gives
purity. At any coefficient place `λ` with the hypotheses of the last
conclusion and `v` not above the residue prime of `λ`, part (b) in degree
`n - 1` then gives the middle-degree Euler polynomial
`reverse((Q v)^{|a|})`.

## Provenance and boundary

Derived from Kottwitz 1992, Theorem 1, p. 657, with purity on p. 661, and from
Clozel 1991, §5.3, pp. 142–144. There the cohomology of the selected
representation is concentrated in the middle degree and the Euler factors are
powers of one degree-`n` polynomial.

This statement does not prove Kottwitz's theorem, concentration, occurrence
with continuity at `λ₀`,
the existence of good charts with the given level, the tensor factorization of
`πf`, or `K`-rationality of `P(πp, F_v)`. These are its named premises. The
comparison of `Q v` with the source Satake parameters and the scalar correction
are later steps (`HarrisKottwitzPowerNormalizationStatement`). The output is
stated at the native PEL universe `Type 0`.
