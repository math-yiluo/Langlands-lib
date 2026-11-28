# Regular local charts for complete discrete valuation rings of mixed characteristic

Module `Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation.Mixed`.

This module is the mixed-characteristic case of the chart construction used in the proof of
`Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximationStatement`, and combines it with
the equal-characteristic case. A complete discrete valuation ring `W'` whose residue field `κ`
has characteristic `p` with `p ≠ 0` in `W'` is a finite extension of a Cohen ring `Λ` of `κ`,
presented by an Eisenstein polynomial: `W' ≅ Λ[X] / (F)` with `X ↦ ϖ`. This is the classical
structure of complete discrete valuation rings of mixed characteristic over Cohen rings (Cohen
rings as in Stacks Project, Tag 0327); the module proves the parts of it that the presentation
theorem `chartConclusion_of_presentation` needs. The
Cohen ring and the map `Λ → W'` come from the package results `exists_cohenRing` and
`IsLocalRing.exists_cohenRing_lift`.

## Expansions in powers of `ϖ`

Throughout, `ψ : Λ → W'` is a ring map to a local ring `W'` whose maximal ideal is `(ϖ)`, and
`ψ` is surjective on residue fields (`residue W' ∘ ψ` surjective).

- `exists_digits`: every `y ∈ W'` has digits `a : ℕ → Λ` and remainders `z : ℕ → W'` with
  `y = ∑_{j < k} ψ(a_j) ϖ^j + ϖ^k z_k` for every `k`. Proof: write each `x ∈ W'` as
  `ψ(b) + ϖ x'` (residue surjectivity and `𝔪 = (ϖ)`), and iterate.
- `exists_fin_digits`: suppose moreover that `W'` is Noetherian, `Λ` is precomplete for `(p)`,
  and `ψ(p) = u ϖ^e` with `u` a unit and `ψ(p) ∈ 𝔪_{W'}`. Then every `y ∈ W'` equals
  `∑_{j < e} ψ(b_j) ϖ^j` for some `b : Fin e → Λ`. Proof: view `W'` as a `Λ`-module through `ψ`.
  By `exists_digits` at order `e`, every `y` is `∑_{j<e} a_j • ϖ^j + p • (u⁻¹ z_e)`; the package
  result `exists_sum_smul_add_pow_smul` (`p`-adic approximation over the precomplete ring `Λ`)
  gives `b` with `y - ∑ ψ(b_j) ϖ^j ∈ ψ(p)^N W' ⊆ 𝔪^N` for all `N`, and the Krull intersection
  theorem (`Ideal.iInf_pow_eq_bot_of_isLocalRing`) makes the difference zero.
- `eq_zero_of_fin_digits`: let `Λ` be a Noetherian local ring with maximal ideal `(p)`, `W'` a
  domain, `ψ` local, `ϖ` irreducible and `ψ(p) = u ϖ^e` with `u` a unit. If
  `∑_{j < e} ψ(c_j) ϖ^j = 0`, then all `c_j` are zero. Proof: first, every `c_j` is divisible by
  `p`: otherwise take the least `j₀` with `c_{j₀} ∉ (p)`; every other term is divisible by
  `ϖ^{j₀+1}` (terms with `j < j₀` because `p ∣ c_j` and `ψ(p) = u ϖ^e` with `j₀ < e`, terms with
  `j > j₀` by their power of `ϖ`), so `ϖ ∣ ψ(c_{j₀})`, which is a unit, a contradiction. Writing
  `c_j = p d_j` and cancelling `ψ(p) ≠ 0`, the `d_j` again satisfy the hypothesis, so by
  induction every `c_j` lies in `(p)^n` for all `n`, and `⋂ (p)^n = 0` (Krull intersection).

## `exists_eisenstein_presentation`

Let `Λ` be a Noetherian local domain with maximal ideal `(p)`, precomplete for `(p)`, and
`ψ : Λ → W'` a local map, surjective on residue fields, to a Noetherian local domain `W'` with
maximal ideal `(ϖ)`, `ϖ` irreducible, and `ψ(p) = u ϖ^e` with `u` a unit and `e > 0`. Then there
is `F ∈ Λ[X]` with

- `F` monic and `F(ϖ) = 0` (evaluation `eval₂ ψ ϖ`);
- the constant coefficient of `F` not in `𝔪_Λ²`;
- every `y ∈ W'` the value at `ϖ` of a polynomial over `Λ`;
- `F` dividing every polynomial over `Λ` that vanishes at `ϖ`.

Proof. By `exists_fin_digits`, `u⁻¹ = ∑_{j<e} ψ(g_j) ϖ^j`. Put `G = ∑_{j<e} p g_j X^j`, of
degree `< e` (`Polynomial.degree_sum_fin_lt`), and `F = X^e - G`, monic of degree `e`. Then
`F(ϖ) = ϖ^e - ψ(p) u⁻¹ = 0`. The constant coefficient is `-p g_0`. Here `g_0` is a unit: otherwise
every term of `u⁻¹ = ∑ ψ(g_j) ϖ^j` lies in `𝔪_{W'}`, since `ψ` is local and `e > 0`. So `p g_0` is
not in `𝔪_Λ² = (p²)`, after cancelling `p ≠ 0`. Surjectivity is `exists_fin_digits`. If `q(ϖ) = 0`,
the remainder `r = q mod F` (`Polynomial.modByMonic`) has degree `< e` and `r(ϖ) = 0`. Thus
`∑_{j<e} ψ(r_j) ϖ^j = 0` (`Polynomial.eval₂_eq_sum_range'`), so all coefficients of `r` vanish by
`eq_zero_of_fin_digits`, and `F ∣ q` (`Polynomial.modByMonic_eq_zero_iff_dvd`).

## `chartConclusion_mixedChar`

Let `W'` be a discrete valuation ring, complete for its maximal ideal, with irreducible element
`ϖ`, whose residue field `κ` has characteristic `p` with `(p : W') ≠ 0`. Then
`ChartConclusion W' C F'` (module
`Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation.Chart`) holds for every finite
type `ℤ`-algebra `C` and every ring map `F' : C → Frac W'`.

Proof.

1. `p` is prime (`CharP.char_is_prime_or_zero`, and `p ≠ 0` since `(p : W') ≠ 0`), and
   `(p : W') ∈ 𝔪_{W'}`.
2. `exists_cohenRing` gives a Cohen ring `Λ` (a complete discrete valuation ring with maximal
   ideal `(p)`, `IsCohenRing p Λ`) and `Λ / (p) ≅ κ`. `IsLocalRing.exists_cohenRing_lift` lifts
   this to `ψ : Λ → W'` with `residue ∘ ψ` equal to the isomorphism composed with the reduction
   map. Hence `ψ` is surjective on residue fields, and `ψ` is local: a non-unit of `Λ` lies in
   `(p)`, so it reduces to zero and its image lies in `𝔪_{W'}`.
3. `(p : W') = v ϖ^n` with `v` a unit (`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`),
   and `n > 0` because `(p : W')` is not a unit.
4. `exists_eisenstein_presentation` gives the presentation `F`. The residue field of `Λ` has
   characteristic `p` (`RingHom.charP_iff_charP` along the field map `ResidueField.map ψ`), so
   `intCast_prime_cases` applies with `(p) = 𝔪_Λ`, and `chartConclusion_of_dvr` (module
   `Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation.Base`) concludes.

## `chartConclusion_of_complete`

For every discrete valuation ring `W'`, complete for its maximal ideal, with an irreducible
element `ϖ`, `ChartConclusion W' C F'` holds for every finite type `ℤ`-algebra `C` and every ring
map `F' : C → Frac W'`. Proof: if `ringChar (ResidueField W')` is zero in `W'` this is
`chartConclusion_equalChar` (module
`Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation.EqualChar`); otherwise it is
`chartConclusion_mixedChar` with `p = ringChar (ResidueField W')`.
