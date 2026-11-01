# Valuation-ring automorphism properties from unique extension

This module proves exactly the published closed proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.ValuationSubringAutPropertiesStatement.{u,v,w,x}`
by the theorem
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.valuationSubringAutProperties`.
Its complete theorem type is that proposition, with no mathematical parameters or
hypotheses outside it. The module imports
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.ValuationSubringAutStatement`
and preserves that module and every imported definition unchanged.

## Source and declaration correspondence

The proof adapts Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`, lines 184–302](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean#L184-L302),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The complete original file has SHA-256
`9eb843515be4be35872451b0d71a3c84a614678ef39b3b577cec6f90f1fa0f45`.
The section telescope is at lines 91–101 and the actual automorphism is at
164–182. All seven original names belong to
`RamificationTheory.HilbertRamification.Higher`. Their adapted names belong to
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`, with the same
short names shown below. The first four retain their original `@[simp]` attributes.

| Item | Original and adapted short name | Original signature | Original proof |
| --- | --- | --- | --- |
| M304.015 | `valuationSubringAutOfUniqueExtension_apply_coe` | 185–191 | 192 |
| M304.016 | `valuationSubringAutOfUniqueExtension_one_apply` | 195–200 | 200 |
| M304.017 | `valuationSubringAutOfUniqueExtension_mul_apply` | 203–212 | 212–214 |
| M304.018 | `valuationSubringAutOfUniqueExtension_apply_inv_apply` | 217–224 | 224 |
| M304.019 | `valuationSubringAutOfUniqueExtension_mem_maximalIdeal_iff` | 228–234 | 234–244 |
| M304.020 | `valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff` | 248–254 | 254–289 |
| M304.021 | `valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff` | 292–299 | 299–302 |

The final theorem `valuationSubringAutProperties` is an internal assembly of
these seven adapted source theorems in the published conjunction order. Its
provenance is exactly those component proofs; it introduces no additional
mathematical assertion or premise.

## Universes, hypotheses and actual objects

The levels `u`, `v`, `w`, `x` are independent. Inside the closed proposition,
`K : Type u` and `L : Type w` carry supplied `Field` and `Algebra K L` instances.
The chosen base DVF has value group in `Type v`, and the chosen target DVF has
value group in `Type x`. The telescope includes the supplied instance
`base.valuation.HasExtension target.valuation` and the explicit hypothesis
`huniq : HasUniqueValuationExtension.{u,v,w,x,x} base target`. The last `x`
is the comparison-valuation universe; it is retained from the original.
The component theorems quantify the same telescope before their local arguments.
The final theorem places it entirely inside its closed proposition.

There are no completeness, finiteness, separability, `IsGalois` or additional
preservation hypotheses. `Gal(L/K)` is the actual group `L ≃ₐ[K] L` for the
supplied algebra. Multiplication applies the right factor first and its inverse
is the inverse algebra equivalence.

Write `R = target.valuationSubring` and
`e σ = valuationSubringAutOfUniqueExtension (base := base) (target := target) huniq σ`.
Here `R` is the actual chosen valuation subring of `L`, whose elements satisfy
`target.valuation a ≤ 1`; `(a : L)` is its subtype coercion. The published
`e σ : R ≃+* R` restricts `σ`, and its inverse restricts `σ⁻¹`. Its membership
witnesses come from the already proved unique-extension preservation theorem.
No new ring, algebra, valuation or automorphism is constructed here.

The ideal `target.maximalIdeal` is exactly `IsLocalRing.maximalIdeal R`.
All ideal memberships and powers are in this ring. The power `m ^ n` is the
ordinary natural ideal power, including `m ^ 0 = ⊤`. The published real-index
ideal is `realRamificationIdeal target s = m ^ realRamificationExponent s`,
where `realRamificationExponent s = (Int.ceil (s + 1)).toNat`. Every real `s`
is allowed without a lower bound.

## Implemented proof of each clause

1. Evaluation after coercion to `L` is `σ (a : L)` by reflexivity of the
   published automorphism's forward map.
2. The identity law `e 1 a = a` is subtype extensionality applied to reflexivity
   of the underlying field values.
3. The multiplication law `e (σ * τ) a = e σ (e τ a)` follows by subtype
   extensionality and reflexivity of composition in `AlgEquiv.aut`. Thus `τ`
   acts first, exactly as in the target.
4. The inverse law is `e σ (e σ⁻¹ a) = a`, with the inverse applied first.
   Subtype extensionality reduces it to `σ.apply_symm_apply` in `L`.
5. For maximal-ideal membership, the proof rewrites membership in a local
   ring's maximal ideal as being a nonunit. A unit `a` maps to a unit under
   the multiplicative map of `e σ`. Conversely, a unit `e σ a` maps to a unit
   under `(e σ).symm`, and simplification gives a unit `a`. Taking these
   two implications for nonunits proves both directions of the required iff.
6. Let `e = e σ` and `m = target.maximalIdeal`. First the proof establishes
   `Ideal.map (e : R →+* R) m = m` by ideal extensionality. Surjectivity of
   `e` characterizes membership in the mapped ideal by a witness `b ∈ m`.
   The forward implication uses clause 5 on `b`; for the reverse implication
   choose `e.symm a` and use clause 5 and the inverse law of the ring equivalence.
   Then `Ideal.map_pow` gives `Ideal.map e (m ^ n) = m ^ n` for every natural
   `n`. If `e a ∈ m ^ n`, map membership supplies `b ∈ m ^ n` with `e b = e a`;
   injectivity gives `b = a`. Conversely, `a ∈ m ^ n` maps into the mapped
   ideal by `Ideal.mem_map_of_mem`, hence into `m ^ n`. This proves the iff
   uniformly, including `n = 0`.
7. The real-index ideal is definitionally the power with exponent
   `realRamificationExponent s`. Applying clause 6 to precisely this natural
   exponent proves the final iff for all real `s`.

The final theorem introduces the complete internal telescope and forms the
seven-clause conjunction from these component theorems. Each component is
specialized with the same `base`, `target`, extension instance and `huniq`.
The theorem therefore proves the exact imported target with its original
binder information, coercions, order of composition and conjunction order.

## Adaptations and attribution

Worker 106 contributed the source extraction, grouped exact target, parameter
analysis and elementary proof-route analysis. Worker 1199 adapted the seven
proofs, implemented their closed assembly and wrote this companion Markdown on
1 November 2026. The adaptation retains all seven source proof bodies, their
hypotheses and short names; prefixes the containing namespaces with
`Langlands.NYLL`; and imports the published statement in place of the original
whole-file imports. It omits the unused pointwise scope, unused universe `y`
and noncomputable section. The new final theorem packages the seven results.
The source partition `notes/reuse/nyll-public-port/m289-m312.md` records no
patch10 change for M304; no compatibility patch is reused in these proofs.

The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` and the original path above.
The attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Its `files/Nyll/ValuedFieldTheory/ANTHROPIC_FLT_SOURCE.md` does not list
`RealLowerGroups.lean`. No applicable errata directory exists in the project,
workspace or Library at preparation.

The original copyright and authorship header is preserved: copyright 2026
Naganori Yamaguchi, authors Naganori Yamaguchi (assisted by OpenAI Codex), under
Apache-2.0. The existing [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain byte-identical to the
pinned source, including inherited notices and earlier-source credits. The Lean
header explicitly records the modifications.

This unit supplies these seven automorphism properties. Genuine lower and upper
ramification groups, Herbrand functions, host inertia and reciprocity remain
separate mathematical work.
