# The weighted Whittaker square estimate for unitary generic representations

Authors: Worker 3657 (proof) and Worker 828 (verification and
submission). Module
`Langlands.Representation.RankinSelberg.UnitaryWeightedWhittakerSquare`,
namespace `Langlands.RankinSelberg.UnitaryGeneric`. Helper module of the Task
6387 proof candidate. It imports `UnitaryWhittakerRestriction` (same candidate), the
published `WeightedWhittakerSquareReduction` (whose public helper lemmas it
reuses), `RecursiveQuotientIntegrationProof` and `Smooth.Schur.Proof`. It
changes no published file.

## Main theorem

```lean
theorem unitaryWeightedWhittakerSquare (n : ℕ) : -- canonical topology of F
    ∀ ψ [IsMulRightInvariant (unipotentHaar F.Carrier n)] μ, IsCompatible … μ →
      ∀ (V : Type uV) … (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V),
        IsAdmissible π → Representation.IsIrreducible π → IsUnitarizable π →
        (∀ (ℓ : glFunctionals ψ n π) f Φ (a : ℝ), 1 / 2 ≤ a →
          Integrable (fun q => (whittakerNorm ψ f.val q) ^ 2 *
            ‖Φ (quotientLastRow n q)‖ ^ 2 * (quotientDeterminantAbs … n q) ^ (2 * a)) μ) ∧
        (∀ (ℓ : glInverseFunctionals ψ n π) f Φ (a : ℝ), 1 / 2 ≤ a →
          Integrable (fun q => (inverseWhittakerNorm ψ f.val q) ^ 2 *
            ‖Φ (quotientLastRow n q)‖ ^ 2 * (quotientDeterminantAbs … n q) ^ (2 * a)) μ)
```

For an irreducible admissible unitarizable `π` of `GL_(n+1)(F)`, every
compatible quotient measure, every coefficient-model Whittaker function `W` (for
the standard or the inverse standard character), every Schwartz–Bruhat `Φ` and
every `a ≥ 1/2`:

`∫_{N \ GL_(n+1)} |W(x)|² |Φ(e_(n+1) x)|² |det x|^(2a) dx < ∞`.

This is the unitary counterpart of the published
`WeightedWhittakerSquareStatement` (square-integrable, `a > 0`).

## Other declarations

- `nonempty_unitaryCentralCharacter_of_unitarizable`: an irreducible admissible
  unitarizable representation of `GL_n(F)` has a unitary central character
  (`UnitaryCentralCharacter`). The published `admissibleSchur_centralCharacter`
  gives a locally constant central character `χ`; its kernel is open. For
  `v ≠ 0` and the invariant positive form `b`, invariance under a central `z`
  gives `conj(χ z) χ z b(v,v) = b(v,v)`, and `b(v,v) ≠ 0`, so `|χ z| = 1`.
- `UnitaryStandardWeightedSquareAt F n`: the standard-character clause in rank
  `n + 1`.
- `unitaryStandardWeightedSquare_zero` (rank one) and
  `unitaryStandardWeightedSquare_succ` (rank `m + 2`); `unitaryStandardWeightedSquare`
  combines them.

## Proof

The proof is that of the published `weightedWhittakerSquare_of` (Worker 724,
reusing lemmas of Worker 676), with these changes.

- **Hypotheses.** Admissibility gives smoothness; the unitary central character
  comes from `nonempty_unitaryCentralCharacter_of_unitarizable` instead of square
  integrability.
- **Rank one.** Unchanged: `|W|` is constant and the determinant power is a
  geometric tail (`a > 0` suffices).
- **Rank `m + 2`.** The recursive quotient integration formula (published
  `recursiveQuotientIntegration`) writes the integral over
  `diag(g,1) · t · k` with density `|det g|⁻¹`. On the support of
  `W(diag(g,1)k)` the determinant is bounded, `|det g| ≤ C_w`, by the published
  `exists_normalizedAbs_det_bound`. The `g`-factor is
  `|det g|⁻¹ · |W|² · |det g|^(2a) = |W|² |det g|^(2a-1) ≤ max(C_w,1)^(2a-1) |W|²`,
  which uses `2a - 1 ≥ 0`. The integral of `|W(diag(g,1))|²` (weight
  `|det g|^0`) is the unitary restriction estimate `unitaryWhittakerRestriction`
  at `k = 0`. The published proof uses the square-integrable estimate with
  weight `|det g|^(-1)` and `max(C_w,1)^(2a)` instead. The `t`-factor is a
  geometric tail.
- **Inverse character.** Unchanged: it is the standard character of
  `x ↦ ψ(-x)`.

## Provenance

- JPSS 1983 (`jpss-1983-rankin-selberg`), §8.3, p.449 (formulas (1)–(2)) and
  p.451 (the weighted square), in the square-integrable case.
- Jacquet–Shalika I (registered as
  `provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`,
  printed page = PDF page + 498), proof of Proposition (1.5)(i), pp.507–508
  (PDF 9–10): the integral is split into the parts `|det p| ≤ 1` and
  `|det p| > 1`; the first is controlled by (1.3.1) at `Re s = 1`, the second by
  gauge estimates. The implemented proof replaces the gauge step by the
  published support bound, as in the square-integrable case.

## Lean checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`: check
4fb4f402 and the builds of the whole candidate; no errors or warnings.
`unitaryStandardWeightedSquare_succ` needs `set_option maxHeartbeats 2000000`.
