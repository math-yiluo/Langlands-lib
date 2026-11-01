# Valuation-ring automorphism laws and preservation properties: statement

This module defines the closed proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.ValuationSubringAutPropertiesStatement`.
It conjoins the signatures of the seven theorems M304.015–.021 from Naganori
Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`, lines 184–303](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean#L184-L303),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The complete source file has SHA-256
`9eb843515be4be35872451b0d71a3c84a614678ef39b3b577cec6f90f1fa0f45`.
Lines 184–303 hold the seven theorems, with their docstrings and proofs. This
module publishes the proposition only. Its proof is reserved for a separate
unit. The proposition takes none of its seven conclusions as a premise.

## Complete proposition

The module imports the published
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.ValuationSubringAut`
and
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.RealIndex`.
In the namespace `Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`,
the complete definition is:

```lean
universe u v w x

def ValuationSubringAutPropertiesStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target),
    (∀ (σ : Gal(L/K)) (a : target.valuationSubring),
      ((valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a :
          target.valuationSubring) : L) = σ (a : L)) ∧
    (∀ a : target.valuationSubring,
      valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq 1 a = a) ∧
    (∀ (σ τ : Gal(L/K)) (a : target.valuationSubring),
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq (σ * τ) a =
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq τ a)) ∧
    (∀ (σ : Gal(L/K)) (a : target.valuationSubring),
      valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ⁻¹ a) = a) ∧
    (∀ (σ : Gal(L/K)) (a : target.valuationSubring),
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a ∈ target.maximalIdeal ↔
        a ∈ target.maximalIdeal) ∧
    (∀ (σ : Gal(L/K)) (n : ℕ) (a : target.valuationSubring),
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a ∈ target.maximalIdeal ^ n ↔
        a ∈ target.maximalIdeal ^ n) ∧
    (∀ (σ : Gal(L/K)) (s : ℝ) (a : target.valuationSubring),
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a ∈
            realRamificationIdeal target s ↔
        a ∈ realRamificationIdeal target s)
```

The declaration has type `Prop` and no declaration parameters. All
mathematical data are quantified inside its body. Its four universe parameters
are independent, and none is fixed to `0`:

| Level | Role |
| --- | --- |
| `u` | Base field carrier `K`. |
| `v` | Chosen base value group `base.ValueGroup`. |
| `w` | Extension field carrier `L`; also the universe of `target.valuationSubring`. |
| `x` | Chosen target value group `target.ValueGroup`; also the comparison universe, the fifth level of `HasUniqueValuationExtension`. |

The shared telescope quantifies over arbitrary field carriers `K` and `L`
with their `Field` instances, an arbitrary `Algebra K L` instance, arbitrary
chosen DVFs `base` on `K` and `target` on `L`, an arbitrary instance
`base.valuation.HasExtension target.valuation`, and an explicit uniqueness
hypothesis `huniq`. The algebra and extension instances are those supplied
in the telescope; none is constructed internally. No completeness,
separability, finite-dimensionality, `IsGalois`, automorphism-preservation or
ramification hypothesis occurs.

## Reused definitions and their meaning

The statement introduces no ring, map, ideal or filtration of its own. It
uses exactly the following published objects.

- `Gal(L/K)` is Mathlib's notation for `L ≃ₐ[K] L`, the `K`-algebra
  automorphisms of `L` for the supplied algebra. Its group law is Mathlib's
  `AlgEquiv.aut`. There `(σ * τ) z = σ (τ z)`, `1` is the identity, and
  `σ⁻¹ = σ.symm`.
- `target.valuationSubring` is the type underlying the actual valuation subring
  `target.valuation.valuationSubring` of `L`. It consists of the `z : L` with
  `target.valuation z ≤ 1`. `target.maximalIdeal` is exactly
  `IsLocalRing.maximalIdeal target.valuationSubring`. Both are abbreviations
  in the published
  `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic`.
- `HasUniqueValuationExtension.{u, v, w, x, x} base target`, from the published
  `RealLowerGroups.UniqueExtension`, says the following. Every valuation `v'`
  on `L` with values in a linearly ordered commutative group with zero
  `Gamma' : Type x`, such that `base.valuation.HasExtension v'` holds, is
  equivalent to `target.valuation`. The comparison universe is `x`, as in
  the source.
- `valuationSubringAutOfUniqueExtension huniq σ`, from the published
  `RealLowerGroups.ValuationSubringAut`, is a ring equivalence
  `target.valuationSubring ≃+* target.valuationSubring`. Its forward map sends
  `a` to `σ (a : L)` and its inverse sends `a` to `σ⁻¹ (a : L)`. Each map comes
  with the membership proof derived from `huniq`. The statement applies this
  equivalence through its function coercion.
- `realRamificationIdeal target s`, from the published `RealLowerGroups.RealIndex`,
  is `target.maximalIdeal ^ realRamificationExponent s` with
  `realRamificationExponent s = (Int.ceil (s + 1)).toNat`.

In the statement, `(a : L)` is the subtype coercion of a ring element into
`L`. Every ideal is an `Ideal target.valuationSubring`, and `∈` is ordinary
ideal membership. `target.maximalIdeal ^ n` is Mathlib's natural power of
ideals, so `n = 0` gives `⊤`.

## Clause-by-clause source correspondence

All original names are in the source namespace
`RamificationTheory.HilbertRamification.Higher`, opened at lines 91–92.
A docstring precedes each theorem, at lines 184, 194, 202, 216, 226–227,
246–247 and 291. The first four theorems carry `@[simp]`.

| Clause | Item | Original theorem | Signature lines | Proof lines |
| --- | --- | --- | --- | --- |
| 1 | M304.015 | `valuationSubringAutOfUniqueExtension_apply_coe` | 185–191 | 192 |
| 2 | M304.016 | `valuationSubringAutOfUniqueExtension_one_apply` | 195–200 | 200 |
| 3 | M304.017 | `valuationSubringAutOfUniqueExtension_mul_apply` | 203–212 | 212–214 |
| 4 | M304.018 | `valuationSubringAutOfUniqueExtension_apply_inv_apply` | 217–224 | 224 |
| 5 | M304.019 | `valuationSubringAutOfUniqueExtension_mem_maximalIdeal_iff` | 228–234 | 234–244 |
| 6 | M304.020 | `valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff` | 248–254 | 254–289 |
| 7 | M304.021 | `valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff` | 292–299 | 299–302 |

Each original signature is `(huniq : HasUniqueValuationExtension.{u, v, w, x, x} base target)`
followed by the local binders below. The adapted clauses are the seven
conjuncts in this order. They keep the source binders, directions and order of
application. Write `e σ` for
`valuationSubringAutOfUniqueExtension (base := base) (target := target) huniq σ`.

1. For all `σ : Gal(L/K)` and `a : target.valuationSubring`,
   `((e σ a : target.valuationSubring) : L) = σ (a : L)`: the automorphism
   evaluates in `L` as the supplied field automorphism.
2. For all `a`, `e 1 a = a`: the identity automorphism induces the identity.
3. For all `σ τ : Gal(L/K)` and `a`, `e (σ * τ) a = e σ (e τ a)`:
   multiplicativity, with `τ` applied first.
4. For all `σ` and `a`, `e σ (e σ⁻¹ a) = a`: applying `e σ` after `e σ⁻¹` gives
   the identity. The source order of application and inverse is kept.
5. For all `σ` and `a`, `e σ a ∈ target.maximalIdeal ↔ a ∈ target.maximalIdeal`.
6. For all `σ`, `n : ℕ` and `a`,
   `e σ a ∈ target.maximalIdeal ^ n ↔ a ∈ target.maximalIdeal ^ n`, including
   `n = 0`.
7. For all `σ`, `s : ℝ` and `a`,
   `e σ a ∈ realRamificationIdeal target s ↔ a ∈ realRamificationIdeal target s`,
   for every real `s` with no lower bound.

The source section at lines 98–101 declares
`{K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]`, an implicit base
`DVF.{u, v} K`, an implicit target `DVF.{w, x} L` and an instance
`[base.valuation.HasExtension target.valuation]`. Lean 4 includes a section
variable in a theorem when the statement mentions it, together with instance
arguments whose variables are all included. Each of the seven signatures
mentions `huniq`, `Gal(L/K)` or the automorphism, and with them `K`, `L`,
`base` and `target`. So every theorem includes the full section telescope,
including the algebra and the extension instance. The closed proposition
quantifies exactly this telescope, with the same binder information. Neither
the source nor this statement assumes completeness, finite dimension or
Galois-ness.

## Organizational adaptations

Conjunction and closure are the only organizational adaptations:

- The seven separate theorem signatures become one conjunction in source order.
- The section telescope and the explicit hypothesis `huniq` are quantified once,
  around the seven-clause conjunction. A universal quantifier over a
  conjunction is equivalent to the conjunction of the universally quantified
  clauses.
- The source's implicit section variables keep their implicit and instance
  binder information inside the closed proposition. In a closed proposition
  this binder information does not change the meaning.
- The local binders `σ`, `τ`, `n`, `s` and `a` are explicit, as in the source.

The statement uses the actual supplied algebra, the actual chosen valuation
ring and maximal ideal, the actual published automorphism with its forward
and inverse maps, and the published real-index ideal. It does not replace them
with abstractly equivalent objects, and no clause is reformulated.

## Proof boundary and module contents

The source proofs on the proof lines above are omitted. This module contains
no theorem proving any clause. A later exact-target proof, bound separately to
this declaration, is expected to establish the proposition.

The module adds the single proposition definition. Elaborating its instance
arguments also produces two auxiliary proof constants:
`ValuationSubringAutPropertiesStatement._proof_1`, a proof of
`SubsemiringClass (ValuationSubring L) L`, and
`ValuationSubringAutPropertiesStatement._proof_2`, a proof of
`IsScalarTower target.valuationSubring target.valuationSubring target.valuationSubring`.
It adds no instance and no new automorphism, ideal, lower or upper ramification
subgroup, Herbrand function, inertia assertion or reciprocity clause. The
real-index property statement and its proof are not used.

## Provenance, attribution and modifications

Worker 106 supplied the source extraction, the grouping of these seven
properties and the parameter analysis, including the closed formulation in
the task contract. Worker 785 checked the formulation against the pinned
original and the published definitions, implemented the module and wrote this
documentation on 1 November 2026. The adaptation prefixes the namespaces with
`Langlands.NYLL` and imports only the published `ValuationSubringAut` and
`RealIndex` modules. It conjoins the seven signatures into one closed
proposition and quantifies the section telescope and `huniq` inside it. It
names the declaration as requested and omits the proofs, the docstrings and
`@[simp]` attributes, and the noncomputable section and pointwise scope. The
source hypotheses and conclusions are mathematically unchanged. The source
partition `notes/reuse/nyll-public-port/m289-m312.md` records no patch10 change
for M304.

The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
at `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the source path
above. Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The supplement's `files/Nyll/ValuedFieldTheory/ANTHROPIC_FLT_SOURCE.md` has no
entry for `RealLowerGroups.lean`. No applicable errata were found in the
project, workspace or current Library.

The original copyright and author header is retained in the Lean file:
copyright 2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all
rights reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex). The
source is released under Apache-2.0. The existing copies of
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged, including the
inherited notices and earlier-source credits. The Lean header records the
modifications.
