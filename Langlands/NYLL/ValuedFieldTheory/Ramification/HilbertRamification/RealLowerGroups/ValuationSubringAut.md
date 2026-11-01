# The actual valuation-ring automorphism from unique extension

This module defines
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension`
in
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.ValuationSubringAut`.
It restricts a supplied algebra automorphism of the field to the chosen
target valuation ring, using uniqueness of valuation extension to prove
that the automorphism and its inverse preserve membership.

## Full telescope and underlying maps

The four universes `u, v, w, x` are independent. The complete telescope is:

```lean
{K : Type u} {L : Type w}
[Field K] [Field L] [Algebra K L]
{base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
{target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
[base.valuation.HasExtension target.valuation]
(huniq :
  Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
    base target)
(σ : Gal(L/K)) :
  target.valuationSubring ≃+* target.valuationSubring
```

Here `u, w` are the field carrier universes and `v, x` are the chosen
value-group universes. The imported five-universe uniqueness predicate is
used at precisely `u, v, w, x, x`, so its comparison value group is in
`Type x`. The extension instance uses the actual `algebraMap K L` from
the supplied algebra. `Gal(L/K)` is Mathlib notation for `L ≃ₐ[K] L`;
the definition has no `IsGalois` or finite-dimensionality hypothesis.

The domain and codomain are both the very chosen
`target.valuationSubring`, the subtype of `L` whose elements satisfy
`target.valuation z ≤ 1`. For `a` in that ring, the forward function is

```lean
a ↦ ⟨σ (a : L), forward_membership⟩
```

and the inverse function is

```lean
a ↦ ⟨σ⁻¹ (a : L), inverse_membership⟩
```

The inverse is the action of the inverse field automorphism in `Gal(L/K)`,
definitionally the symmetric algebra equivalence. Both maps retain their
actual underlying values in `L`.

## Membership and structure proofs

The module imports
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.AutomorphismProof`
and reuses its theorem
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension`.
This theorem has the published closed proposition as its complete type.
Each application explicitly specializes its four universes, fields,
supplied field and algebra instances, chosen `base` and `target`, extension
instance, uniqueness hypothesis, automorphism and element. Underscores in
these applications infer the instances already in the displayed telescope.

For the forward witness, the specialized theorem gives

```lean
(a : L) ∈ target.valuation.valuationSubring ↔
  σ (a : L) ∈ target.valuation.valuationSubring
```

Its `.1` direction applies to `a.property`. The inverse witness uses exactly
the same specialization with `σ⁻¹` in place of `σ`, again taking `.1`.
The definition therefore reuses the published valuation-preservation proof
for both maps.

The ring equivalence's `left_inv` and `right_inv` fields are respectively
`Subtype.ext (σ.symm_apply_apply a)` and
`Subtype.ext (σ.apply_symm_apply a)`. Its `map_mul'` and `map_add'` fields
are `Subtype.ext` applied to `map_mul σ (a : L) (b : L)` and
`map_add σ (a : L) (b : L)`. These are the actual supplied field
automorphism laws lifted to the valuation-ring subtype. They are structural
proofs inside this definition.

## Exact source correspondence

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`, lines 164–182](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean#L164-L182).
The complete source file has SHA-256
`9eb843515be4be35872451b0d71a3c84a614678ef39b3b577cec6f90f1fa0f45`.
Lines 1–235 were read for this adaptation, including the uniqueness
predicate, preservation lemma, complete definition and subsequent
property signatures.

| Original at the pinned commit | Adapted declaration or construction |
| --- | --- |
| `RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension`, lines 166–182 | `Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension`, retaining the original short name and structure fields. |
| `RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension`, lines 48–52 | Reuse `Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension` at comparison universe `x`. |
| `RamificationTheory.DiscreteValuationField.DVF.mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension`, lines 70–86 | Reuse the published theorem under the `Langlands.NYLL` prefix, specializing its closed proposition explicitly. |
| Supplied fields, chosen DVFs and extension, lines 98–101; uniqueness and automorphism, lines 167–170 | Preserve their order, all four independent universes, the supplied algebra and the actual chosen valuation ring. |
| Forward and inverse subtype constructors, lines 171–178 | Preserve `σ` and `σ⁻¹` as the underlying functions and take the forward direction of the corresponding membership iff. |
| Inverse, multiplication and addition proofs, lines 179–182 | Preserve the four `Subtype.ext` proofs. |

The source partition records no patch10 change for M304. The preceding
real-index declarations are source-order neighbors; this construction
uses the uniqueness predicate and preservation theorem directly.

## Attribution and modification record

Worker 1199 isolated and adapted this definition and wrote its Markdown
on 1 November 2026. Worker 106 contributed the source extraction, focused
grouping and parameter analysis. Modifications prefix the namespaces,
replace the broad upstream NYLL import with the published preservation
module, keep Mathlib Galois support, explicitly specialize the closed
preservation theorem, and omit unrelated declarations and unused source
context (`y`, `noncomputable section` and pointwise scope). The original
forward/inverse formulas and four structure proofs are retained.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained: copyright 2026
Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex). The source is Apache-2.0. The existing
verbatim [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged;
the NOTICE has no `RealLowerGroups.lean` entry. The workspace, project
and current-Library errata directories were absent when checked.

The approved environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. This module adds the single
actual ring equivalence. Public evaluation and automorphism laws,
maximal-ideal and ideal-power preservation, real-index preservation and
ramification subgroups remain separate units.
