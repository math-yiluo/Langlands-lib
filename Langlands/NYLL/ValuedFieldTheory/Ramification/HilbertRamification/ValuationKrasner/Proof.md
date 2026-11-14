# NYLL M397.001: valuation Krasner stabilizer step (proof)

This module proves the existing Library proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_eq_of_fixed_of_closeStatement`
by the theorem
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_eq_of_fixed_of_close`.
Its type is exactly the closed proposition at the four independent universes
`u, v, w, x`. The statement and its imported definitions are unchanged.

## Parameters and conclusion

The target quantifies over fields `K : Type u` and `L : Type w`, a `K`-algebra
structure on `L`, and discrete valuation field structures
`base : DVF.{u, v} K` and `target : DVF.{w, x} L`. It retains both the instance
`base.valuation.HasExtension target.valuation` and the supplied uniqueness
predicate `HasUniqueValuationExtension.{u, v, w, x, x} base target`.
Thus the two field universes and the two value-group universes remain
independent, with the uniqueness comparison universe specialized to `x`
as in the published action and source theorem.

Write `R = target.valuationSubring` and, for this explanation only,
`A = valuationSubringAutOfUniqueExtension (base := base) (target := target) huniq σ`,
where `σ : Gal(L/K)`. This is the published ring automorphism of `R`
induced by the supplied field automorphism. For any `a b : R`, the hypotheses
are precisely `hfix : A b = b` and
`hclose : A a ≠ a → addVal R (A a - a) < addVal R (a - b)`.
The conclusion is `A a = a`. Here `addVal` is Mathlib's normalized additive
valuation with values in `ℕ∞`, with zero sent to `⊤`. There is no assumption
that the extension is finite dimensional or Galois, and no completeness
assumption.

## Implemented argument

After introducing the complete target telescope, the proof assumes
`hne : A a ≠ a` and derives a contradiction. Since `A` is a ring equivalence
and `A b = b`, `map_sub` gives `A (a - b) = A a - b`. The published theorem
`addVal_valuationSubringAutOfUniqueExtension`, applied to `a - b`, therefore
gives

```text
addVal R (A a - b) = addVal R (a - b).
```

The additive valuation preserves negation, so `b - a = -(a - b)` also gives
`addVal R (b - a) = addVal R (a - b)`. The proof applies Mathlib's
`IsDiscreteValuationRing.addVal_add` to `A a - b` and `b - a`. Their sum is
`A a - a`; after the two equalities above, its conclusion simplifies to

```text
addVal R (a - b) ≤ addVal R (A a - a).
```

This contradicts `hclose hne` by `not_le_of_gt`. The two elementary difference
identities are proved with `ring`. The argument works directly in `ℕ∞`,
including its top element, and needs no nonzero case split or conversion to
integer-valued valuations.

The imports are the exact target module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationKrasner.Statements`
and the published invariance proof module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RamificationDepth.ActionProof`.
The latter supplies M323.001 by its Lean name. Its implementation specializes
the published `IsDiscreteValuationRing.addVal_smul` to the ring-automorphism
action; this module reuses that result without copying its proof.

## Development check

The approved Lean-service check in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) compiled the module with zero
errors and zero warnings. Declaration inspection reported the independent
level parameters `["u", "v", "w", "x"]` and only `propext`, `Classical.choice`,
and `Quot.sound` as axioms. This is development evidence; exact-target
validation and independent semantic review are separate acceptance checks.

## Source and modifications

The proof is adapted from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationKrasner.lean`,
lines 45–111](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationKrasner.lean#L45-L111).
The section telescope is at lines 27–36, the theorem signature at lines 45–62,
and its proof at lines 63–111. The entire retained file (lines 1–116) was read;
its SHA-256 is
`80a7e3430c526226a0f830de5afaab50dd6476169a847e9b5ff74ef7c2f1ee8c`.
The readable retained file is
[/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationKrasner.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationKrasner.lean>).

Worker 578 adapted the source on 14 November 2026 by prefixing the namespace
with `Langlands.NYLL`, replacing the signature with the exact published closed
Prop target and introducing its complete telescope, narrowing the imports,
and removing the unnecessary `noncomputable section`. The elementary proof
route and both source hypotheses are preserved. The source's introductory
finite-Galois prose is broader in assumptions than its actual theorem
telescope; this proof follows the exact general telescope.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No matching NYLL erratum was present in the workspace or current Library
errata directories; the separate project notes errata directory was absent.
The original copyright, author and Apache-2.0 notices are retained in the Lean
header. The existing [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) apply unchanged.
