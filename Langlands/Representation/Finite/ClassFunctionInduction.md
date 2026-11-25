# Induction of class functions

`Langlands.Representation.Finite.ClassFunctionInduction`. For a finite group `G`, a subgroup `H` and a
function `φ : G → K` into a field, `Langlands.FiniteRep.inducedClassFunction H φ` is the normalized
induced function

```text
inducedClassFunction H φ g = |H|⁻¹ * ∑ x : G, [x⁻¹ g x ∈ H] φ (x⁻¹ g x).
```

The file gives its elementary calculus: conjugation invariance, linearity, the projection formula
against a conjugation-invariant function, induction from `⊤`, and induction in stages. It is the
function-level operation used by Solomon's theorem (`SolomonInduction`), the monomial case
(`MonomialTrace`) and Brauer's theorem in trace form (`BrauerTrace`), and by the degree-zero Brauer
argument (`DegreeZeroBrauerSupport`).

This is an operation on functions; `φ` need not be a class function, only its values on `H` matter,
and nothing here constructs an induced representation. The Library's actual induction is
`Langlands.FiniteRep.induceRep` (`Induction`); `InducedCharacterProof` proves that its character is
given by the same formula.

## Statements

All in namespace `Langlands.FiniteRep`, with `{G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]`.

- `inducedClassFunction (H : Subgroup G) (φ : G → K) : G → K`, defined with classical decidability of
  membership in `H`.
- `inducedClassFunction_apply`: the defining formula, for any `[DecidablePred (· ∈ H)]`.
- `inducedClassFunction_congr`: if `φ x = ψ x` for all `x ∈ H`, then
  `inducedClassFunction H φ = inducedClassFunction H ψ`.
- `inducedClassFunction_conj`: `inducedClassFunction H φ (y⁻¹ * g * y) = inducedClassFunction H φ g`.
- Linearity: `inducedClassFunction_add` (`H (φ + ψ) = H φ + H ψ`), `inducedClassFunction_zero`,
  `inducedClassFunction_const_mul` (scalar `c` comes out), `inducedClassFunction_sum` (finite sums
  `∑ i ∈ s`).
- `inducedClassFunction_mul_of_conj_invariant`: for `f` with `f (x⁻¹ * g * x) = f g`,
  `inducedClassFunction H φ g * f g = inducedClassFunction H (fun y => φ y * f y) g`.
- `inducedClassFunction_top_of_conj_invariant` (`[CharZero K]`): for conjugation-invariant `φ`,
  `inducedClassFunction ⊤ φ = φ`.
- `inducedClassFunction_inducedClassFunction` (`[CharZero K]`, `[Fintype H]`): for `L : Subgroup H` and
  `ψ : H → K`, inducing from `H` the extension by zero of `inducedClassFunction L ψ` equals inducing
  from `L.map H.subtype` the extension by zero of `ψ`.

## Proofs

Each identity is a manipulation of the finite sum. Conjugation invariance reindexes the sum by
`x ↦ y * x`. The projection formula moves the invariant factor `f g = f (x⁻¹ g x)` inside the sum.
For `⊤` every term equals `φ g` and the factor `|G|⁻¹ * |G|` cancels. Induction in stages writes the
inner induction as `|L|⁻¹ ∑_{y ∈ H} F (x y)` with `F z = [z⁻¹ g z ∈ L] ψ (z⁻¹ g z)` (and shows that the
term vanishes when `x⁻¹ g x ∉ H`), exchanges the two sums, reindexes `x ↦ x y` for each `y ∈ H`, and
cancels `|H|`, using `|L.map H.subtype| = |L|`.

## Declarations

In order, all in `Langlands.FiniteRep`: def `inducedClassFunction`; theorems `inducedClassFunction_apply`,
`inducedClassFunction_congr`, `inducedClassFunction_conj`, `inducedClassFunction_add`,
`inducedClassFunction_zero`, `inducedClassFunction_const_mul`, `inducedClassFunction_sum`,
`inducedClassFunction_mul_of_conj_invariant`, `inducedClassFunction_top_of_conj_invariant`,
`inducedClassFunction_inducedClassFunction`.

## Source and licence

Adapted from one file of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`):

| FLT file | SHA-256 |
| --- | --- |
| `Definitions/Def_ClassFunction_Induced.lean` | `44cee0b2389dc811a40237bd840ed7ad22cb56179202ed494a04427ecb0e0e48` |

The SHA-256 values are those recorded for the FLT files in the evidence appendix of the Library's
audit `notes/reuse/anthropic-brauer-audit.md`.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not list
this file as containing third-party material.

### Changes against the FLT file

- Namespace `ClassFunction` becomes `Langlands.FiniteRep`; `ClassFunction.induced` becomes
  `inducedClassFunction`, `induced_X` becomes `inducedClassFunction_X`, `induced_induced` becomes
  `inducedClassFunction_inducedClassFunction`.
- `import Mathlib` is replaced by the four Mathlib modules used. No option is set (the FLT package sets
  `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false` and `autoImplicit false`); every proof checks
  under Lean's defaults.
- In `inducedClassFunction_conj` the final `simp only` leaves a goal that holds by definition (two
  decidability instances for the same proposition); it is closed by `rfl`. Without the FLT option
  `backward.isDefEq.respectTransparency.types false` the `simp only` no longer closes it.
- Lemma names deprecated in the pinned Lean are replaced by their successors (`if_true` → `ite_true`,
  `if_pos` → `ite_eq_left`, `dif_pos` → `dite_eq_left`, `if_neg` → `ite_eq_right`).
- Docstrings and this page are added; statements and proofs are otherwise the FLT text.

## Literature

Jean-Pierre Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977) (literature
`serre-1977-linear-representations`), read in the library copy:

- §7.2, printed p.55: the induced class function `Ind_H^G(f)(s) = (1/h) Σ_{t ∈ G, t⁻¹st ∈ H} f(t⁻¹st)`,
  `h = Card(H)`, the formula of `inducedClassFunction`. Proposition 20, p.56: it is a class function,
  and the character of the induced representation when `f` is a character.
- §7.2, Remark (3), p.57: `Ind(ψ · Res φ) = (Ind ψ) · φ`, the content of
  `inducedClassFunction_mul_of_conj_invariant`.
- §7.1, remark (3), p.55: transitivity of induction (for representations); here proved directly for
  the formula as `inducedClassFunction_inducedClassFunction`.
