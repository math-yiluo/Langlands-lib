# Reduction of the restriction-square estimate to the torus lattice sum

Author: Worker 381.

This module proves the conditional theorem
`Langlands.RankinSelberg.SquareIntegrableWhittakerRestriction.of_torusSum`:

```lean
theorem of_torusSum
    (hIw : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ),
      QuotientIwasawaIntegrationStatement F T n)
    (hSum : IwasawaTorusSumStatement.{uF})
    (hB1 : SquareIntegrableWhittakerTorusSumStatement.{uF, uV}) :
    SquareIntegrableWhittakerRestrictionStatement.{uF, uV}
```

So the published restriction-square estimate (formula (7) of JPSS 1983
§8.3) follows from three propositions: the quotient Iwasawa integration
formula, the discrete torus decomposition of that formula, and the torus
lattice square-summability `SquareIntegrableWhittakerTorusSumStatement`. The
theorem does not prove any of the three. It uses no other hypothesis and only
the standard axioms.

The first two propositions are proved in the Library
(`Langlands.RankinSelberg.quotientIwasawaIntegration` in
`Langlands.Representation.RankinSelberg.QuotientIwasawaIntegrationProof` and
`Langlands.RankinSelberg.iwasawaTorusSum` in
`Langlands.Representation.RankinSelberg.IwasawaTorusSumProof`). The module
supplies them in

```lean
theorem of_squareIntegrableWhittakerTorusSum
    (hB1 : SquareIntegrableWhittakerTorusSumStatement.{uF, uV}) :
    SquareIntegrableWhittakerRestrictionStatement.{uF, uV}
```

defined as `of_torusSum (fun _ _ F T n => quotientIwasawaIntegration F T n)
iwasawaTorusSum hB1`. Its only hypothesis is the torus lattice
square-summability, which this module does not prove.

## Notation

Fix `p`, `F`, `T`, `n`, `k`, `ψ`, a right-invariant `unipotentHaar`, a
measure `μ` on `N_(n+1) \ GL_(n+1)(F)` compatible with `generalLinearHaar`
and `unipotentHaar`, and `π` on `GL_r(F)` with `r = n + (0 + k + 1) + 1`,
irreducible and square-integrable, with `ℓ` and a coefficient-model vector
`f`. Write `W = f.val.val`, `t = n + 1`, `d = 0 + k + 1` and
`e = appendIdentity n d : GL_t(F) → GL_r(F)`, so `e g = diag(g, 1_d)`. The
integrand of the target is

`Φ(N g) = ‖W(e g)‖² · |det g|^(-d)`,

which is `restrictedWhittakerNorm ψ k f.val q ^ 2 *
quotientDeterminantAbs (normalizedAbsoluteValue T) n q ^ (-(d : ℝ))` in Lean.
Let `K = GL_t(𝒪)` (`Conductor.integralSubgroup`), `dk` the restriction of
`generalLinearHaar F.Carrier n` to `K`, `ϖ` a uniformizing element from
`Iwasawa.exists_isUniformizingElement`, and for `λ : Fin t → ℤ`

`δ_t(λ) = ∏_{i<j} |ϖ^(λ_i) / ϖ^(λ_j)|`,
`q_λ(x) = N · (ϖ^λ x)`,

where `ϖ^λ = Iwasawa.torus ϖ λ`.

## Helper results

- `continuous_of_rightInvariant`: a function on a topological group invariant
  under right translation by an open subgroup is locally constant, hence
  continuous.
- `prod_pairs_div`, `prod_padOne`, `modulus_padZero`: closed forms for the
  pairwise-ratio product `∏_{i<j} c_i / c_j`, used to compute the modulus of a
  zero-padded exponent vector: padding `a` by `d` zeros multiplies the modulus
  by `(∏_i g(a_i))^d` whenever `g 0 = 1`.
- `extendExp n d a : Fin (n + d) → ℤ` pads `a : Fin (n + 1) → ℤ` by zeros;
  `snoc_extendExp` identifies `Fin.snoc (extendExp n d a) 0` with the
  zero-padding to length `n + d + 1` (for `0 < d`), and `extendExp_injective`
  shows the padding is injective.
- `appendIdentity_torus`, `appendIdentity_torus_snoc`:
  `diag(ϖ^a, 1_d) = ϖ^(Fin.snoc (extendExp n d a) 0)` as an element of
  `GL_(n+d+1)`.
- `modulus_snoc_extendExp`, `inverseModulus_snoc_extendExp`: the weight
  identity
  `δ_(n+d+1)(Fin.snoc (extendExp n d a) 0)⁻¹ = δ_t(a)⁻¹ · |det ϖ^a|^(-d)`,
  which is `δ_r(diag(a, 1_d))⁻¹ = δ_t(a)⁻¹ |det a|^(-d)` for the torus
  element `a = ϖ^λ`.
- `continuous_appendIdentity`: `e` is continuous (iterated
  `GeneralLinear.rankInclusionContinuous 1`).

## Proof of `of_torusSum`

1. **Measure.** `hIw p F T n μ hμ` rewrites `μ` as the pushforward of
   `δ⁻¹ · (da × dk)` along `(a, x) ↦ N a x`, and `hSum p F T n ϖ hϖ` rewrites
   that as `μ = Σ_λ ofReal(δ_t(λ)⁻¹) • map q_λ dk`, a countable sum over
   `λ : Fin t → ℤ`.
2. **Smoothness and a finite cover.** Square-integrability gives
   admissibility, hence smoothness; `model_isSmooth` gives an open subgroup
   `L ≤ GL_r(F)` with `W(y l) = W(y)` for `l ∈ L`. Its preimage
   `H = e⁻¹(L)` is an open subgroup of `GL_t(F)`. Since `K` is compact
   (`Conductor.isCompact_levelOpenSubgroup` at level `0`), finitely many
   translates `ρ H`, `ρ ∈ S`, cover `K`. For `x ∈ K` in `ρ H`,
   `W(y · e x) = W(y · e ρ)`, so
   `‖W(y · e x)‖² ≤ Σ_{ρ ∈ S} ‖W(y · e ρ)‖²`.
3. **Measurability.** `W` is continuous by `continuous_of_rightInvariant`;
   `g ↦ |det g|` is continuous by `T.determinantNormContinuous`; both descend
   to the quotient by `Continuous.quotient_lift`, and `|det|` is positive, so
   `Φ` is continuous, hence a.e. strongly measurable and measurable. Each
   `q_λ` is continuous.
4. **Pointwise bound on each orbit.** For `x ∈ K`, `|det x| = 1`
   (`Conductor.valuation_det_of_mem_integralSubgroup`), so
   `Φ(q_λ x) ≤ C(λ) := Σ_{ρ ∈ S} ‖W(e(ϖ^λ) · e ρ)‖² · |det ϖ^λ|^(-d)`.
5. **One orbit.** By `lintegral_smul_measure`, `lintegral_map` and
   `lintegral_mono_ae` on `K`, together with `dk(univ) = 1`
   (`generalLinearHaar_integralSubgroup`),
   `∫ Φ d(ofReal(δ_t(λ)⁻¹) • map q_λ dk) ≤ ofReal(δ_t(λ)⁻¹ C(λ))`.
   By the weight identity and `appendIdentity_torus_snoc`,
   `δ_t(λ)⁻¹ C(λ) = Σ_{ρ ∈ S} a_ρ(λ)` with
   `a_ρ(λ) = δ_r(s(λ))⁻¹ ‖W_ρ(ϖ^(s(λ)))‖²`, where
   `s(λ) = Fin.snoc (extendExp n d λ) 0` and `W_ρ = W(· e ρ)` is the
   Whittaker function of the right translate `modelRepresentation π ℓ (e ρ) f`.
6. **Summability.** `hB1` at rank `m = n + d`, applied to the coefficient
   vector `modelRepresentation π ℓ (e ρ) f`, gives summability of
   `ν ↦ δ_r(Fin.snoc ν 0)⁻¹ ‖W_ρ(ϖ^(Fin.snoc ν 0))‖²` over `ν : Fin (n + d) → ℤ`.
   Composing with the injective map `extendExp n d` (`Summable.comp_injective`)
   gives summability of `a_ρ`; the finite sum
   over `S` is summable (`summable_sum`).
7. **Assembly.** With `hasFiniteIntegral_iff_ofReal` and
   `lintegral_sum_measure`, the lower integral of `Φ` against `μ` is at most
   `Σ'_λ ofReal(Σ_{ρ ∈ S} a_ρ(λ)) = ofReal(Σ'_λ Σ_{ρ ∈ S} a_ρ(λ)) < ∞`
   (`ENNReal.ofReal_tsum_of_nonneg`). With step 3 this gives
   `Integrable Φ μ`.

## Provenance

The target is formula (7) of Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983), §8.3, pp. 449–450.
The source argues in three steps; in its notation `r - t = d`.

- Its premise (p. 449) is that the elements of `𝒲(π; ψ)` are `K`-finite
  and square-integrable modulo `N_r Z_r`.
- With the integration formula (1) for an integral over `N_r \ G_r`, it
  deduces formula (2), p. 449:
  `∫_{N_(r-1) \ G_(r-1)} |W(diag(g, 1))|² |det g|^(-1) dg = ‖W‖² < ∞`.
- For `r > t`, the integration formula (6), p. 450, writes an integral
  `∫_{N_(r-1) \ G_(r-1)} F(g) |det g|^(-1) dg` as an iterated integral over
  `g ∈ N_t \ G_t`, `h ∈ N_(r-t-1) \ G_(r-t-1)` and a compact variable, with
  weight `|det g|^(-(r-t)) |det h|^(t-1)`. Applied to (2), it gives (7), an
  integral over `N_t \ G_t`.

The implemented route is different and is internal to this project. It uses
none of the formulas (1), (2) and (6). In place of the premise modulo
`N_r Z_r` it uses the torus lattice square-summability
`SquareIntegrableWhittakerTorusSumStatement`. That proposition says that
`δ_r(ϖ^(Fin.snoc ν 0))⁻¹ ‖W(ϖ^(Fin.snoc ν 0))‖²` is summable over
`ν : Fin (r - 1) → ℤ`. The exponent vectors with last entry `0` represent
the torus lattice modulo the centre `Z_r`, so this is a derived,
measure-free counterpart of square-integrability modulo `N_r Z_r`. Its
published proof starts from square-integrable matrix coefficients modulo
the centre. The reduction then integrates directly over `N_t \ G_t`, using the
Iwasawa decomposition of the quotient measure
(`QuotientIwasawaIntegrationStatement`, `IwasawaTorusSumStatement`). The
weight identity in step 5, `δ_r(diag(a, 1_d)) = δ_t(a) |det a|^d`, is the
discrete counterpart of the weight `|det g|^(-(r-t))` in formula (6).
