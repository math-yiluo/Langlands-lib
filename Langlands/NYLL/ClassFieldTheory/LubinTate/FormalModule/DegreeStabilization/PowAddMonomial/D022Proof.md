# Low-degree coefficients of `(H + c X^d) ^ n - H ^ n` (NYLL M351.022)

This module proves the published proposition
`Langlands.NYLL.PortInternal.M351.d022Statement` by the theorem
`Langlands.NYLL.PortInternal.M351.d022`. It imports the published statement
module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.PowAddMonomial.Statements`,
which is not changed, and `Mathlib.Algebra.Ring.GeomSum` for `geom_sum₂_mul`.

## Target and mathematical meaning

The theorem lives in namespace `Langlands.NYLL.PortInternal.M351` and has the
target's exact binders: implicit `R : Type*` with `[CommRing R]`, implicit
`τ : Type*` (independent universes `u_1` and `u_2`), implicit
`H : MvPowerSeries τ R`, then `hH : MvPowerSeries.constantCoeff H = 0`,
`q d : τ →₀ ℕ`, `hq : q.degree ≤ d.degree`, `hd : 1 ≤ d.degree`, `c : R` and
`n : ℕ`; the binders from `hH` through `n` are explicit. Its type is `d022Statement hH q d hq hd c n`, which
unfolds to

```
MvPowerSeries.coeff q ((H + MvPowerSeries.monomial d c) ^ n - H ^ n) =
  if n = 1 then (if q = d then c else 0) else 0
```

where `q.degree` is Mathlib's `Finsupp.degree` (the sum of the exponents) and
`q = d` is decided by the instance fixed in the statement module.

Mathematically: let `H` have zero constant coefficient and let `c X^d` be a
monomial of total degree at least one. Then in every exponent `q` of total
degree at most `d.degree`, the power `(H + c X^d) ^ n` has the same
coefficient as `H ^ n`, except that for `n = 1` the coefficient at `q = d`
grows by `c`.

## Implemented proof

Write `M = monomial d c` and `A = H + M`.

1. `unfold d022Statement` exposes the proposition.
2. `hd0 : d ≠ 0`: if `d = 0`, then `hd` says `1 ≤ (0 : τ →₀ ℕ).degree`, which
   `simp` refutes.
3. `rcases n with _ | _ | n` splits into `n = 0`, `n = 1` and `n + 2`.
4. Case `n = 0`: `simp` reduces both sides to `0`, since
   `A ^ 0 - H ^ 0 = 1 - 1 = 0` and `0 ≠ 1`.
5. Case `n = 1`: after `classical`, `simp only [zero_add, pow_one,
   add_sub_cancel_left, ↓reduceIte]` reduces the goal to
   `coeff q M = if q = d then c else 0`. This is Mathlib's
   `MvPowerSeries.coeff_monomial q d c`; `convert` closes the goal, the only
   difference being the `Decidable (q = d)` instance (any two such instances
   are equal).
6. Case `n + 2`, where the right-hand side is `0`:
   - `hM : constantCoeff M = 0`, proved as in M351.021 by
     `coeff_zero_eq_constantCoeff_apply` and `coeff_monomial_ne` from `hd0`.
   - `rw [← geom_sum₂_mul, add_sub_cancel_left, MvPowerSeries.coeff_mul_monomial]`
     rewrites `A ^ (n + 2) - H ^ (n + 2)` as `S * (A - H)` with the geometric
     sum `S = ∑ i ∈ range (n + 2), A ^ i * H ^ (n + 2 - 1 - i)`, then
     `A - H` as `M`, and the coefficient as
     `if d ≤ q then coeff (q - d) S * c else 0`.
   - `hS : constantCoeff S = 0`: after pushing `constantCoeff` through the
     sum, products, powers and the sum `H + M` and using `hH` and `hM`, each
     summand is `0 ^ i * 0 ^ (n + 2 - 1 - i)`. For `i = 0` the second exponent
     is `n + 1 > 0` and for `i = j + 1` the first is positive, so `simp` shows
     every summand is `0`.
   - `simp only [show n + 1 + 1 ≠ 1 by omega, ↓reduceIte]` reduces the
     right-hand side to `0`, and `split_ifs with hdq` splits on `d ≤ q`.
   - If `d ≤ q`: since `Finsupp.degree` is additive,
     `(q - d).degree + d.degree = q.degree` (by `map_add` and
     `tsub_add_cancel_of_le hdq`), so `hq` and `omega` give
     `(q - d).degree = 0`, hence `q - d = 0` by `Finsupp.degree_eq_zero_iff`.
     Then `coeff (q - d) S = coeff 0 S = constantCoeff S = 0` and
     `0 * c = 0`.
   - Otherwise the left-hand side is already `0` and `rfl` closes the goal.

No auxiliary declaration, instance or simp attribute is added.

## Source correspondence

The original is the private theorem
`LubinTate.SameUniformizer.coeff_pow_add_monomial_sub_pow_of_degree_le`,
type at lines 612–620 and proof at lines 621–680.

| Original | Adapted |
| --- | --- |
| Lines 612–620: binders and conclusion | Same binders; conclusion `d022Statement hH q d hq hd c n` (step 1) |
| Line 621: `classical` | Used only in the `n = 1` case (step 5) |
| Lines 622–626: `hd0` by `subst`, `map_zero` and `omega` | Step 2, by `rintro rfl` and `simp` |
| Lines 627–629: case `n = 1` by `simp [MvPowerSeries.coeff_monomial]` | Step 5, by `simp only` and `convert MvPowerSeries.coeff_monomial q d c` |
| Lines 630–631: case `n = 0` by `simp only` | Step 4, by `simp` |
| Lines 632–680: case `n + 1 ≥ 2` by an order bound | Step 6, by a direct coefficient computation (see below) |

For `n ≥ 2` the source shows that `A ^ n - H ^ n` has order at least
`d.degree + 1`: M351.021 and Mathlib's
`MvPowerSeries.one_le_order_iff_constCoeff_eq_zero` give `1 ≤ order H` and
`1 ≤ order A`; the private order estimate M351.009
(`order_sub_add_pred_le_order_pow_sub_pow_stabilization`) gives
`order M + (n - 1) ≤ order (A ^ n - H ^ n)`; M351.005
(`degree_le_order_monomial_stabilization`) gives `d.degree ≤ order M`; and
`MvPowerSeries.coeff_of_lt_order` gives the vanishing of the coefficient at
`q`, since `q.degree < d.degree + 1`. The implemented proof instead factors
the difference as `S * M` and reads off the coefficient. It thus uses neither
order estimate, whose published theorems `Langlands.NYLL.PortInternal.M351.d005`
and `d009` (Task 6075) are not needed, nor M351.021, whose two-line argument
is repeated as `hM`.

## Adaptations

All modifications to the selected source declaration are:

- Make the private theorem public under the stable internal name
  `Langlands.NYLL.PortInternal.M351.d022` instead of
  `LubinTate.SameUniformizer.coeff_pow_add_monomial_sub_pow_of_degree_le`.
- State the conclusion as the published `d022Statement hH q d hq hd c n`,
  opened by `unfold`.
- Replace the order-theoretic proof of the case `n ≥ 2` by the geometric-sum
  coefficient computation above, and restate the other cases' tactic steps
  as listed in the table.
- Import the published statement module and `Mathlib.Algebra.Ring.GeomSum`
  instead of the source imports
  (`Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient` and
  `Mathlib.RingTheory.MvPowerSeries.Trunc`).
- Omit the source module's other declarations, its section variables (unused
  here), `noncomputable section` and local `Classical.propDecidable`
  instance; the statement module fixes the decidability of `q = d`.
- Add a module title, a docstring and a dated modification record.

## Attribution, licence and environment

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)", followed by a dated modification record. The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already
in the Library and are not modified.

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`
(SHA-256 `2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`),
readable under `n-yamaguchi-0729--ClassFieldTheory/source/` in registered
source `external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` (content
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The [port partition](../../../../../../../notes/reuse/nyll-public-port/m337-m360.md#m351)
lists this unit in module M351. No patch10 edit applies.

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). There the module
compiles with no errors or warnings, and the theorem has universe parameters
`u_1` and `u_2` and depends only on `propext`, `Classical.choice` and
`Quot.sound`. Compilation is not acceptance: publication under
`lean.proof@1` also requires the Lake build, exact-target and
unchanged-statement checks, independent semantic review and integration.

## Shared draft provenance

Worker 492 supplied the complete proof and documentation as revision 1 of
the public draft for Task 6725 (`2b0858ba-350c-4984-a75d-a5e4f6a746ae`),
content key `5edf8a1455db7540a1c429b5139786c3b7142829bde1f74b6e94d7fb88c56d66`,
on 14 November 2026. Worker 185 adopted that proof unchanged on
16 November 2026, checked the source correspondence and the current
statement/import files, clarified the binder description, and added this
provenance and the dated adoption record. Worker 492 is retained as a
coauthor of the submission.
