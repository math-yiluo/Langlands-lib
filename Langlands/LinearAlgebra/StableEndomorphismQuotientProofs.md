# Successive kernel and range quotients: kernels, images and exactness (proofs)

Author: Worker 969.

This module proves the closed statement targets of
`Langlands/LinearAlgebra/StableEndomorphismQuotientStatements.lean`, which it
imports unchanged. Through that file it uses the public construction
`Langlands.LinearAlgebra.StableEndomorphismQuotients`, also unchanged. The
targets formalize David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, Appendix C.II, proof of
Lemma (iv), printed page 278 / PDF page 284 (registered source
`renard-2026-representations-groupes-reductifs-padiques`). The statement
Markdown records how the targets correspond to the source and why the
arbitrary-ring form is an internal strengthening. The proof below does not
follow the source text step by step. It argues directly with elements.

All declarations are in the namespace
`Langlands.LinearAlgebra.StableEndomorphism`.

## Exported theorems

| Theorem | Proves exactly |
| --- | --- |
| `powerQuotientExactnessAt t k` | `PowerQuotientExactnessAt t k`, for every `R : Type uR` with `[Ring R]`, every `V : Type uV` with `[AddCommGroup V] [Module R V]`, every `t : Module.End R V` and every `k : ℕ` |
| `powerQuotientExactSequenceStatement` | `PowerQuotientExactSequenceStatement.{uR, uV}` |
| `complexPowerQuotientExactSequenceStatement` | `ComplexPowerQuotientExactSequenceStatement.{uV}` |
| `powerQuotientExactSequenceStatements` | `PowerQuotientExactSequenceStatements.{uR, uV}`, the aggregate target |

Each theorem has the published proposition as its type and adds no
hypotheses. The ring may be noncommutative or zero. The module may be zero
or of any size. The index may be `0`, where `N_0 = 0` and `I_0 = V`. No
finiteness, stabilization, chain condition or nontriviality is assumed.
The aggregate theorem depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

The ten clauses of `PowerQuotientExactnessAt t k` are also exported as
separate theorems, listed with their proofs below.

## Notation

This notation is used only in this Markdown:

- `N_j = kerPow t j` and `I_j = rangePow t j`;
- `E_j = KerQuotient t j = N_(j+1) / N_j` and
  `F_j = RangeQuotient t j = I_j / I_(j+1)`;
- `[x]` is the class of `x` under `kerQuotientMk` or `rangeQuotientMk`;
- for an ambient submodule `S` of `V`, the image of `S` in `E_k` is
  `(S.comap (kerPow t (k + 1)).subtype).map (kerQuotientMk t k)`, and its
  image in `F_k` is
  `(S.comap (rangePow t k).subtype).map (rangeQuotientMk t k)`.
  These are the forms used in the statement.

## Helper results

Section `Ambient` works in `V`.

- `apply_pow_apply` and `pow_apply_apply` give
  `t (t ^ k x) = t ^ (k + 1) x` and `t ^ k (t x) = t ^ (k + 1) x`. They come
  from `pow_succ'`, `pow_succ` and `Module.End.mul_apply`.
- `map_kerPow_succ t j` proves `(kerPow t (j + 1)).map t = range t ⊓ kerPow t j`.
  The forward inclusion uses the public `apply_mem_kerPow`. For the reverse
  inclusion, if `t x ∈ N_j` then `t ^ (j + 1) x = t ^ j (t x) = 0`.
- `pow_apply_mem_rangePow_succ_iff` says that for `x ∈ N_(k+1)`,
  `t ^ k x ∈ I_(k+1)` iff `x ∈ N_k ⊔ (range t ⊓ N_(k+1))`. Forward: if
  `t ^ k x = t ^ (k + 1) y`, then `x - t y ∈ N_k`. Hence
  `t y = x - (x - t y) ∈ N_(k+1)`, using the public `kerPow_le_succ`, and
  `x = (x - t y) + t y`. Backward: if `x = a + t c` with `a ∈ N_k`, then
  `t ^ k x = t ^ (k + 1) c`.
- `apply_mem_rangePow_succ_succ_iff` says that for `w ∈ I_k`,
  `t w ∈ I_(k+2)` iff `w ∈ I_(k+1) ⊔ (N_(k+1)).map (t ^ k)`. Forward: write
  `w = t ^ k x` and `t w = t ^ (k + 2) z`. Then `x - t z ∈ N_(k+1)`, and
  `w = t ^ (k + 1) z + t ^ k (x - t z)`. Backward: if
  `w = t ^ (k + 1) c + t ^ k x` with `x ∈ N_(k+1)`, then
  `t w = t ^ (k + 2) c`.

Section `Images` works in the quotients.

- `kerQuotientMk_eq_iff` and `rangeQuotientMk_eq_iff` restate
  `Submodule.Quotient.eq` for the two quotients, using the public
  `mem_kerPowInSucc` and `mem_rangePowSuccIn` and `Submodule.coe_sub`:
  `[x] = [y]` iff `x - y ∈ N_k` (resp. `x - y ∈ I_(k+1)`).
- `kerQuotientMk_mem_map_comap_iff`: if `N_k ≤ S`, then for `x ∈ N_(k+1)`,
  `[x]` lies in the image of `S` in `E_k` iff `x ∈ S`. If `[y] = [x]` with
  `y ∈ S`, then `y - x ∈ N_k ≤ S`, so `x = y - (y - x) ∈ S`
  (`sub_sub_cancel`). `rangeQuotientMk_mem_map_comap_iff` is the same
  statement for `F_k`, assuming `I_(k+1) ≤ S`.

Every ambient submodule in the ten clauses contains the relevant
denominator by `le_sup_left`. So each clause about a submodule of `E_k` or
`F_k` is proved by `ext`. Then a class is written as `[x]` using the public
`kerQuotientMk_surjective` or `rangeQuotientMk_surjective`, and the
membership is reduced to `V` by the lemma above.

## The ten clauses

Clause numbers follow the conjunct order of `PowerQuotientExactnessAt`.

1. `ker_kerShiftMk`: `ker (kerShiftMk t k) = kerPowInSucc t (k + 1)`.
   For `x ∈ N_(k+2)`, the public `kerShiftMk_apply`,
   `kerQuotientMk_eq_zero_iff`, `coe_kerShift_apply` and `mem_kerPow` reduce
   both sides to `t ^ k (t x) = 0` and `t ^ (k + 1) x = 0`. These agree by
   `pow_apply_apply`.
2. `ker_kerToRangeQuotient`. The class `[x]` is in the kernel iff
   `t ^ k x ∈ I_(k+1)`, by the public `kerToRangeQuotient_mk`,
   `rangeQuotientMk_eq_zero_iff` and `coe_kerToRange_apply`. Then apply
   `pow_apply_mem_rangePow_succ_iff`.
3. `range_kerToRangeQuotient`. If `[t ^ k x] = [w]`, then
   `w = (w - t ^ k x) + t ^ k x` with `w - t ^ k x ∈ I_(k+1)`. Conversely, if
   `w = a + t ^ k x` with `a ∈ I_(k+1)` and `x ∈ N_(k+1)`, then `[x]` maps to
   `[w]` because `t ^ k x - w = -a` (`sub_add_cancel_right`).
4. `kerQuotientShift_injective`. Unfold `kerQuotientShift` as the public
   `liftQ` of `kerShiftMk`. Mathlib's `Submodule.ker_liftQ_eq_bot`, applied
   to clause 1, gives a zero kernel, and `LinearMap.ker_eq_bot` turns that
   into injectivity.
5. `range_kerQuotientShift_eq_map`. This is clause 6 after rewriting
   `(kerPow t (k + 2)).map t` into `range t ⊓ kerPow t (k + 1)` with
   `map_kerPow_succ t (k + 1)`. The index `k + 2` is the corrected index of
   the source.
6. `range_kerQuotientShift`. If `[x]` is the image of `[z]` with
   `z ∈ N_(k+2)`, then `t z - x ∈ N_k` by the public `kerQuotientShift_mk`.
   So `x = (x - t z) + t z`, with `t z ∈ range t ⊓ N_(k+1)` by
   `apply_mem_kerPow`. Conversely, if `x = a + t c` with `a ∈ N_k` and
   `t c ∈ N_(k+1)`, then `c ∈ N_(k+2)`, and `[c]` maps to `[x]` because
   `t c - x = -a`.
7. `rangeQuotientShift_surjective`. A class in `F_(k+1)` is `[w]` with
   `w = t ^ (k + 1) v`. It is the image of `[t ^ k v]`, by the public
   `rangeQuotientShift_mk`, `apply_pow_apply` and `Subtype.ext`.
8. `ker_rangeQuotientShift`. The class `[w]` is in the kernel iff
   `t w ∈ I_(k+2)`, by the public `rangeQuotientShift_mk`,
   `rangeQuotientMk_eq_zero_iff` and `coe_rangeShift_apply`. Then apply
   `apply_mem_rangePow_succ_succ_iff`.
9. `range_kerQuotientShift_eq_ker` is clause 6 followed by clause 2
   reversed.
10. `range_kerToRangeQuotient_eq_ker` is clause 3 followed by clause 8
    reversed.

`powerQuotientExactnessAt t k` is the anonymous-constructor conjunction of
these ten theorems, in order.

## The closed targets

- `powerQuotientExactSequenceStatement` applies `powerQuotientExactnessAt` to
  arbitrary `R`, `V`, `t` and `k`.
- `complexPowerQuotientExactSequenceStatement` specializes the ring-general
  theorem at `R := ℂ`, with universe `uR := 0`:
  `powerQuotientExactSequenceStatement.{0, uV} ℂ V t k`.
- `powerQuotientExactSequenceStatements` pairs the two.

## Scope

The module proves only the ten identities of the statement module. It does
not prove the common-first-stabilization theorem or the C.II
finite-localization proposition on printed page 279 / PDF page 285. It also
says nothing about general categorical exactness, power-kernel-union
localization or the adapter to the book's possibly nonunital module actions.
