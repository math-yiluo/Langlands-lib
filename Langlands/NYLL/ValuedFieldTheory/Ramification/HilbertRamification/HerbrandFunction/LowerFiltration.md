# Integral lower ramification filtration of a unique valuation extension

The module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LowerFiltration`
defines the actual integral lower filtration of the supplied unique valuation
extension. It adapts exactly M305.001 of Naganori Yamaguchi's
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/HerbrandFunction.lean`, lines 32–52](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/HerbrandFunction.lean#L32-L52).
The complete original file has SHA-256
`a094355ce3645fe924eb8575233a874ca16007f91ab9bafe99f13c33cd3a878c`.
Original lines 1–63, including both imports, the shared telescope and the
following projection theorem, were read directly.

## Exact declaration map and full telescope

| Unit | Original declaration | Adapted declaration |
| --- | --- | --- |
| M305.001, signature at 40–43 and value at 44–52 | `RamificationTheory.HilbertRamification.Higher.lowerRamificationFiltrationOfUniqueExtension` | `Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.lowerRamificationFiltrationOfUniqueExtension` |

The adapted declaration has four independent universe parameters `u, v, w, x`.
Its complete mathematical telescope and result are:

```lean
∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
  {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
  {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
  [base.valuation.HasExtension target.valuation]
  (huniq :
    Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
      base target),
  Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration
    Gal(L/K)
```

The fields `K, L`, base and target DVFs are implicit, the two field structures, algebra and valuation-extension
instance are supplied, and `huniq` is explicit. The valuation value groups have
universes `v` and `x`, independently of the field carriers in `u` and `w`.
The final `x` of `HasUniqueValuationExtension` is the comparison-valuation
universe, as in the original. The algebra and supplied extension instance are
those of these same fields and valuations.

The group `Gal(L/K)` is Mathlib's actual algebra automorphism group
`L ≃ₐ[K] L`, with its inferred universe and standard composition law.
No unrelated group or transported field is substituted. The result is a
value of the published generic three-field structure, whose projections are
`lower`, `lower_normal` and `antitone`.

## Construction and its laws

The definition fills those three fields directly:

```lean
lower n := lowerRamificationGroup
  (base := base) (target := target) huniq (n : ℝ)
lower_normal n := lowerRamificationGroup_normal
  (base := base) (target := target) huniq (n : ℝ)
antitone := by
  intro m n hmn
  apply lowerRamificationGroup_antitone
    (base := base) (target := target) huniq
  exact_mod_cast hmn
```

Every natural index, including zero, is sent by the canonical natural-to-real
cast to the public actual real lower group for these supplied data. For
`R = target.valuationSubring` and `m = target.maximalIdeal`, the existing
`mem_lowerRamificationGroup_nat_iff` explains this subgroup: an actual
`σ : Gal(L/K)` belongs precisely when

```text
valuationSubringAutOfUniqueExtension huniq σ a - a ∈ m ^ (n + 1)
```

for every `a : R`, with the same implicit `base` and `target`. The restricted
automorphism evaluates as `σ (a : L)`. Both displacement and ideal membership
are in the actual valuation subring of the supplied `L`. This interpretation
uses the previously proved public carrier theorem; this module adds no new
membership or projection theorem.

The stored normality proof is the published
`lowerRamificationGroup_normal` specialized to `(n : ℝ)`. That theorem proves
normality inside the actual algebra automorphism group for every real index.
The antitonicity field introduces natural indices `m, n` and `hmn : m ≤ n`,
applies the published real-index `lowerRamificationGroup_antitone`, then uses
`exact_mod_cast hmn` to prove `(m : ℝ) ≤ (n : ℝ)`. Consequently the stored
inclusion is `lower n ≤ lower m`, in the decreasing direction. The cast
step is purely order compatibility of the canonical embedding.

These laws are proved within the construction from the public theorems;
neither law is an input premise. There is no finite-dimensionality,
finite-group, `IsGalois`, completeness, residue-separability or extra
arithmetic-law premise. In particular, the finite-dimensional section that
begins at original line 65 does not apply to this definition. The source's
`noncomputable section` is retained.

## Focused dependencies and modifications

The module imports by Lean name exactly:

- `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.RamificationQuotients.Filtration`,
  for the generic structure and its existing normality projection instance.
- `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.LowerGroupProof`,
  for the actual lower groups and the proved real normality and antitonicity.

The latter import supplies the actual group definition and its valued-field
prerequisites transitively. The former replaces the needed small portion of
the original wholesale `Nyll.ValuedFieldTheory.Ramification.Herbrand.Function`
import. The entire real-lower-groups source import is replaced by the focused
published proof module. The namespace gains `Langlands.NYLL`; the uniqueness
predicate and result structure are explicitly qualified. The source
construction, binder kinds, universes, arguments, index cast and proof terms
are retained. The unused source namespace opening is omitted, and the module
and declaration documentation describe the extracted unit.

Native searches of the current Library and approved Mathlib number-theory
and group-theory sources found no existing same-name or complete-field
`toLowerRamificationFiltration` declaration to reuse. The host
`Langlands.Ramification.lowerGroup` constructs subgroups for a supplied action
on a local ring and has a different interface. This module reuses the
published NYLL actual group family, the generic filtration bundle and
Mathlib's actual automorphism group, natural/real casts, subgroup inclusion
and normality, without introducing replacements. The public declaration
partition `notes/reuse/nyll-public-port/m289-m312.md` records no patch10 change
for M305. Its conservative source-order edges are scheduling information.

Only M305.001 is implemented. The following source projection theorem
M305.002, finite-group instance, generic and arithmetic Herbrand functions,
inverse functions, upper groups, host inertia and reciprocity conclusions
remain separate work.

## Attribution

The registered original source is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the original
path above. The attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No workspace, project or supplied-Library `notes/errata` directory was
present at preparation. The root NOTICE does not list this source file
among its third-party paths.

The original copyright and authorship are retained: copyright 2026 Naganori
Yamaguchi, all rights reserved; authors Naganori Yamaguchi (assisted by
OpenAI Codex). Apache-2.0 applies. The existing verbatim
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged,
including inherited third-party notices. Their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

Worker 106 contributed the source/interface extraction and the actual
lower-group proof routing. Worker 1199 independently read the original and
published interfaces, implemented the extraction and wrote this companion
on 1 November 2026. The Lean header records the modifications.
The approved environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, distinct from upstream's
Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
