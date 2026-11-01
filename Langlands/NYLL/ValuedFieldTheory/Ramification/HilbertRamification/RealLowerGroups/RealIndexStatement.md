# Real-index exponent and ideal properties: statement

This module defines the closed proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.RealRamificationIndexPropertiesStatement`.
It conjoins the signatures of the eight elementary property theorems
M304.005–.008 and M304.010–.013 from Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`, lines 111–162](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean#L111-L162),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The complete source file has SHA-256
`9eb843515be4be35872451b0d71a3c84a614678ef39b3b577cec6f90f1fa0f45`.
The exponent theorems occupy lines 111–135 and the ideal theorems lines
142–162, including their docstrings and proofs. This module publishes the
proposition only. Its proof is reserved for a separate unit, and the
proposition takes none of its eight conclusions as a premise.

## Complete proposition

The module imports the published
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.RealIndex`.
In the namespace `Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`,
the complete definition is:

```lean
universe w x

def RealRamificationIndexPropertiesStatement : Prop :=
  Monotone realRamificationExponent ∧
  realRamificationExponent (-1) = 0 ∧
  (∀ {s : ℝ}, s ≤ -1 → realRamificationExponent s = 0) ∧
  (∀ n : ℕ, realRamificationExponent (n : ℝ) = n + 1) ∧
  (∀ {L : Type w} [Field L]
      (target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L),
    (∀ {s t : ℝ}, s ≤ t → realRamificationIdeal target t ≤ realRamificationIdeal target s) ∧
    realRamificationIdeal target (-1) = ⊤ ∧
    (∀ n : ℕ, realRamificationIdeal target (n : ℝ) = target.maximalIdeal ^ (n + 1)) ∧
    (∀ {s : ℝ}, s ≤ -1 → realRamificationIdeal target s = ⊤))
```

The declaration has type `Prop` and no declaration parameters. All
mathematical data are quantified inside its body. Its two universe parameters
are independent, and neither is fixed to `0`:

| Level | Role |
| --- | --- |
| `w` | Field carrier `L` of the ideal clauses; also the universe of `target.valuationSubring`. |
| `x` | Chosen value group `target.ValueGroup`. |

Both universes occur only in the fifth conjunct. The four exponent clauses
have no field, valuation, universe or typeclass parameters. The four ideal
clauses share one quantification over an implicit field carrier `L`, a supplied
`Field L` instance and an explicit chosen DVF `target`. These are arbitrary.
No base field, algebra structure, valuation extension, uniqueness,
completeness, separability, finite-dimensionality, Galois, automorphism or
filtered-reciprocity hypothesis occurs.

## Reused definitions and their conventions

The statement reuses exactly the published definitions; it introduces no new
exponent, ideal, ring or filtration:

```lean
def realRamificationExponent (s : ℝ) : ℕ :=
  (Int.ceil (s + 1)).toNat

def realRamificationIdeal {L : Type w} [Field L]
    (target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L)
    (s : ℝ) : Ideal target.valuationSubring :=
  target.maximalIdeal ^ realRamificationExponent s
```

`Int.ceil (s + 1)` is the least integer at least `s + 1`. `Int.toNat` sends
nonpositive integers to `0` and positive integers to the corresponding natural
number. These are the ceil and `Int.toNat` indexing of the original. No
alternative formula, such as a floor or an untruncated exponent, replaces them.

The chosen ring `target.valuationSubring` is the type underlying the actual
subring `target.valuation.valuationSubring` of `L`, consisting of the
`z : L` with `target.valuation z ≤ 1`. The ideal
`target.maximalIdeal` is exactly `IsLocalRing.maximalIdeal target.valuationSubring`.
Both are abbreviations in the published
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic`.
Every ideal in the statement is an `Ideal target.valuationSubring`. There, `≤`
is ideal inclusion and `⊤` is the top of the ordinary ideal lattice, the whole
valuation ring. The power `target.maximalIdeal ^ (n + 1)` is Mathlib's natural
power of ideals, the same power used in the published definition body. Here
`n + 1` is natural-number addition and `(n : ℝ)` is the natural-number cast.
`Monotone f` is Mathlib's `∀ ⦃a b⦄, a ≤ b → f a ≤ f b`, for the usual orders
on `ℝ` and `ℕ`.

## Clause-by-clause source correspondence

All original names are in the source namespace
`RamificationTheory.HilbertRamification.Higher`, opened at lines 91–92.
Docstrings occupy the line before each signature; four theorems carry `@[simp]`.

| Clause | Item | Original theorem | Signature lines | Original statement |
| --- | --- | --- | --- | --- |
| 1 | M304.005 | `realRamificationExponent_mono` | 112–113 | `Monotone realRamificationExponent` |
| 2 | M304.006 | `realRamificationExponent_neg_one` | 120–121 | `realRamificationExponent (-1) = 0` |
| 3 | M304.007 | `realRamificationExponent_eq_zero_of_le_neg_one` | 125–127 | `{s : ℝ} (hs : s ≤ -1) : realRamificationExponent s = 0` |
| 4 | M304.008 | `realRamificationExponent_nat` | 133–134 | `(n : ℕ) : realRamificationExponent (n : ℝ) = n + 1` |
| 5 | M304.010 | `realRamificationIdeal_antitone` | 143–144 | `{s t : ℝ} (hst : s ≤ t) : realRamificationIdeal target t ≤ realRamificationIdeal target s` |
| 6 | M304.011 | `realRamificationIdeal_neg_one` | 148–149 | `realRamificationIdeal target (-1) = ⊤` |
| 7 | M304.012 | `realRamificationIdeal_nat` | 153–154 | `(n : ℕ) : realRamificationIdeal target (n : ℝ) = target.maximalIdeal ^ (n + 1)` |
| 8 | M304.013 | `realRamificationIdeal_eq_top_of_le_neg_one` | 158–160 | `{s : ℝ} (hs : s ≤ -1) : realRamificationIdeal target s = ⊤` |

Clauses 1–4 are the first four conjuncts. Clauses 5–8 are, in this order, the
four conjuncts inside the fifth conjunct. Each clause keeps its source
direction:

1. the exponent is monotone;
2. its value at `-1` is `0`;
3. it vanishes at every `s ≤ -1`;
4. at a natural index `n` it equals `n + 1`;
5. for `s ≤ t`, the ideal at `t` is contained in the ideal at `s`;
6. the ideal at `-1` is `⊤`;
7. at a natural index `n` the ideal is the `(n + 1)`-st power of the actual
   chosen maximal ideal;
8. the ideal at every `s ≤ -1` is `⊤`.

The source section at lines 98–101 declares
`{K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]`, an implicit base
`DVF.{u, v} K`, an implicit target `DVF.{w, x} L` and an instance
`[base.valuation.HasExtension target.valuation]`. Lean 4 includes a section
variable in a theorem only when the statement mentions it, together with
instance arguments whose variables are all included. No exponent theorem
mentions a section variable. Each ideal theorem mentions only `target`, so its
effective telescope begins `{L : Type w} [Field L] {target : DVF.{w, x} L}`.
The base, algebra and extension variables do not occur in any of the eight
signatures, so the closed statement omits them.

## Organizational adaptations

Conjunction and closure are the only organizational adaptations:

- The eight separate theorem signatures become one conjunction in source order.
- The ideal clauses quantify `L`, `[Field L]` and `target` once, around their
  four-clause conjunction. A universal quantifier over a conjunction is
  equivalent to the conjunction of the universally quantified clauses.
- The source's implicit section variable `target` becomes an explicit binder of
  the closed proposition. In a closed proposition this binder information does
  not change the meaning.
- The named hypotheses `hs` and `hst` become anonymous implication premises.
  The implicit `{s : ℝ}` and `{s t : ℝ}` binders and the explicit `n : ℕ`
  binders keep their source binder information.

The statement keeps the ceil and `Int.toNat` exponent, the actual chosen
valuation ring and the actual chosen maximal ideal. It does not reformulate the
clauses with a different ordering, filtration or normalization.

## Proof boundary and module contents

The source proofs, at lines 114–117, 122, 128–130, 135, 145, 150, 155 and
161–162, are omitted. This module contains no theorem proving any clause. A
later exact-target proof, bound separately to this declaration, is expected to
establish the proposition.

The module adds the single proposition definition. Elaboration of its instance
arguments also produces two auxiliary proof constants:
`RealRamificationIndexPropertiesStatement._proof_1`, a proof of
`SubsemiringClass (ValuationSubring L) L`, and
`RealRamificationIndexPropertiesStatement._proof_2`, the proof
`IsScalarTower.right` of
`IsScalarTower target.valuationSubring target.valuationSubring target.valuationSubring`.
It adds no instance and no valuation-ring automorphism, ideal-preservation
statement, lower or upper ramification group, Herbrand function, inertia
assertion or reciprocity clause. It does not depend on M304.003 or its proof.

## Provenance, attribution and modifications

Worker 106 supplied the source extraction, the grouping of these eight
properties and the parameter analysis, including the exact closed formulation
in the task contract. Worker 1045 checked the formulation against the pinned
original and the published definitions, implemented the module and wrote this
documentation on 1 November 2026. The adaptation prefixes the namespace with
`Langlands.NYLL` and imports only the published `RealIndex` module. It
conjoins the eight signatures into one closed proposition, quantifying the
field and chosen DVF inside the ideal clauses. It names the declaration as
requested and omits the unused section parameters, the proofs, the docstrings
and `@[simp]` attributes, and the noncomputable section and pointwise scope.
The source hypotheses and conclusions have no mathematical change. The source
partition `notes/reuse/nyll-public-port/m289-m312.md` records no patch10 change
for M304.

The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
at `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the source path
above. Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The supplement's `files/Nyll/ValuedFieldTheory/ANTHROPIC_FLT_SOURCE.md` lists
four other valuation-theory files and no entry for `RealLowerGroups.lean`.
No applicable errata were found in the project, workspace or current Library.

The original copyright and author header is retained in the Lean file:
copyright 2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all
rights reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex). The
source is released under Apache-2.0. The existing copies of
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged, including the
inherited notices and earlier-source credits. The Lean header records the
modifications.
