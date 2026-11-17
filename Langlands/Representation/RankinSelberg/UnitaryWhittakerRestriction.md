# The restriction estimate for unitary generic Whittaker functions

Authors: Worker 3657 (proof) and Worker 828 (verification and
submission). Module
`Langlands.Representation.RankinSelberg.UnitaryWhittakerRestriction`, namespace
`Langlands.RankinSelberg.UnitaryGeneric`. Helper module of the Task 6387 proof
candidate. It imports `UnitaryWhittakerTorusSum` (same candidate) and the published
`SquareIntegrableWhittakerRestrictionReduction`, whose public lemmas it reuses.
It changes no published file.

## Main theorem

```lean
theorem unitaryWhittakerRestriction (n k : ℕ) : -- canonical topology of F
    ∀ ψ [IsMulRightInvariant (unipotentHaar F.Carrier n)] μ,
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ (V : Type uV) … (π : Representation ℂ
          (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V),
        IsAdmissible π → Representation.IsIrreducible π → IsUnitarizable π →
        ∀ (ℓ : glFunctionals ψ (n + (0 + k + 1)) π)
          (f : (coefficientModel π ℓ).toSubmodule),
          Integrable (fun q => restrictedWhittakerNorm ψ k f.val q ^ 2 *
            quotientDeterminantAbs (normalizedAbsoluteValue F.canonicalTopologicalData) n q ^
              (-(((0 + k : ℕ) : ℝ)))) μ
```

That is, for every compatible quotient measure `μ` on `N_(n+1) \ GL_(n+1)(F)`,

`∫ |W(diag(g, 1_(k+1)))|² |det g|^(-k) dμ(g) < ∞`.

For `k = 0` this is the square-integrability of `W` on `N \ P` with respect to
the right-invariant measure. The published statement for square-integrable
representations, `SquareIntegrableWhittakerRestrictionStatement`, has the weight
`|det g|^(-(k+1))` instead; this module does not assert that weight for unitary
representations.

## Other declarations

- `summable_density_mul_model_sq`: the torus sum of `UnitaryWhittakerTorusSum`
  for coefficient-model vectors (a coefficient-model vector is
  `g ↦ ℓ(π(g) v)` by the published `modelMap_surjective`).
- `density_extendExp`: padding an exponent vector `a ∈ ℤ^(n+1)` by `k` zeros
  multiplies the inverse modulus by `|det ϖ^a|^(-k)`. Proof: the published
  `modulus_padZero` with `d = 0 + k`.

## Proof

This is the proof of the published
`SquareIntegrableWhittakerRestriction.of_torusSum` (Worker 381), with three
changes.

1. The measure: `μ = Σ_lam δ(ϖ^lam)⁻¹ · (k ↦ [ϖ^lam k])_* dk` by the published
   `QuotientTorusEnvelope.quotientMeasure_eq_sum_torus` (equivalent to the
   quotient Iwasawa formula with the torus sum used there).
2. The weight is `|det g|^(-k)`. On the orbit of `ϖ^lam`, after the finite cover
   of `GL_(n+1)(O)` by right translates under which `W` is invariant, the mass is
   bounded by `Σ_ρ δ(ϖ^lam)⁻¹ |det ϖ^lam|^(-k) |W_ρ(diag(ϖ^lam, 1_(k+1)))|²`.
   By `density_extendExp` and the published `appendIdentity_torus_snoc` this is
   `Σ_ρ δ_(n+k+1)(lam, 0_k)⁻¹ |W_ρ(diag(ϖ^(lam,0_k), 1))|²`, where `δ_(n+k+1)` is
   the inverse modulus of `GL_(n+k+1)`.
3. Summability over `lam` is the unitary torus sum
   `summable_density_mul_model_sq` for `GL_(n+k+2)` (rank parameter `n + k`),
   composed with the injective padding `extendExp`.

The rest (continuity, finite cover, assembly with `lintegral_sum_measure`) is
unchanged.

## Provenance

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg
  convolutions*, Amer. J. Math. 105 (1983), 367–464, registered as
  `jpss-1983-rankin-selberg`: §8.3, formulas (2) and (7), pp.449–450, in the
  square-integrable case. The unitary exponent `-k` replaces `-(k+1)`; the
  `k = 0` case is Jacquet–Shalika I, (1.3.1), p.507 (see
  `UnitaryWhittakerTorusSum.md`).
- The route is internal: the published reduction of Worker 381 with the
  unitary torus sum.

## Lean checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`: check
f8118bba and the builds of the whole candidate; no errors or warnings. The main
theorem needs `set_option maxHeartbeats 2000000`.
