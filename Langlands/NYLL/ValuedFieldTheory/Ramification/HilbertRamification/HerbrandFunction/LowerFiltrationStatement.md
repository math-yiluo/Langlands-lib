# Natural-level projection of the actual lower filtration: statement

The module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LowerFiltrationStatement`
defines the closed proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.LowerRamificationFiltrationProjectionStatement`.
It states exactly the natural-level projection identity M305.002 from
Naganori Yamaguchi's *ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/HerbrandFunction.lean`, lines 55–63](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/HerbrandFunction.lean#L55-L63).
The complete original file has SHA-256
`a094355ce3645fe924eb8575233a874ca16007f91ab9bafe99f13c33cd3a878c`.
Original lines 1–100 were read directly, including the shared telescope at
32–35, construction at 40–52, projection documentation at 55, signature at
56–62 and proof at 63.

## Exact proposition and binder kinds

The declaration has type `Prop`, with four independent universe parameters
`u, v, w, x` and no mathematical parameters outside its body. Its entire
body is:

```lean
∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
  {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
  {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
  [base.valuation.HasExtension target.valuation]
  (huniq :
    Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
  (n : ℕ),
  (lowerRamificationFiltrationOfUniqueExtension
    (base := base) (target := target) huniq).lower n =
    lowerRamificationGroup
      (base := base) (target := target) huniq (n : ℝ)
```

Here both construction names are in
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`. The field
carriers `K : Type u` and `L : Type w` are implicit. The field structures,
`Algebra K L` and the valuation-extension instance are supplied instance
binders. The DVFs `base` and `target` are implicit, with value-group
universes `v` and `x` independent of the field universes. Both `huniq` and
`n` are explicit. The final `x` in
`HasUniqueValuationExtension.{u, v, w, x, x}` is the comparison-valuation
universe, exactly as in the original signature.

The same supplied algebra, extension instance and uniqueness predicate
appear on both sides. The proposition introduces no finite-dimensionality,
finite-group, completeness, `IsGalois`, residue-separability or additional
filtration-law premise. The source's finite-dimensional assumption begins
only at line 65 and does not apply to M305.002.

## Meaning of the equality

The left side is the `lower` field at `n` of the published actual
`lowerRamificationFiltrationOfUniqueExtension`. That construction packages
the genuine real lower groups with their existing normality and
antitonicity proofs. The right side is the published actual
`lowerRamificationGroup` for the same `base`, `target` and `huniq`, evaluated
at the canonical natural-to-real cast `(n : ℝ)`.

Both sides are subgroups of the same actual `Gal(L/K)`, Mathlib's algebra
automorphism group `L ≃ₐ[K] L`. This is equality of those subgroups, rather
than an isomorphism or a statement about a replacement generic filtration.
Every natural index is quantified, including zero. Normality and
antitonicity are already stored in the filtration and are not premises of
this proposition.

This unit defines the proposition and does not supply a proof of it. The
original source proves the projection by `rfl`; the separately bound proof
unit will establish the exact published target. No projection theorem or
simp lemma is introduced here. The adapted source theorem name
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.lowerRamificationFiltrationOfUniqueExtension_lower`
is reserved for that proof unit.

## Source correspondence and modifications

| Source item | Adapted item |
| --- | --- |
| Shared telescope, lines 32–35 | The same binder kinds inside the closed proposition |
| M305.002 signature, lines 56–62 | The body of `LowerRamificationFiltrationProjectionStatement` |
| Source proof, line 63, and `@[simp]` attribute | Deferred to the separate proof unit |

The internal universal closure is an organizational adaptation of the
source theorem signature, not a new assertion attributed to the
literature. Its mathematical content is exactly the original equality
under exactly the original supplied data. The Lean namespace gains
`Langlands.NYLL`; the DVF and uniqueness predicate are explicitly
qualified. The single import is the published
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LowerFiltration`,
which supplies both actual constructions and all their prerequisites.
Its Lean/Markdown pair and every imported pair are reused unchanged.
The source's noncomputable section is unnecessary for this Prop
definition and is omitted.

The public partition `notes/reuse/nyll-public-port/m289-m312.md` identifies
M305.001 and M305.002 and records no patch10 change for this source module.
Its conservative source-order edges are scheduling information, not extra
mathematical hypotheses. Native searches found no existing projection
target or same-name theorem to reuse. This extraction covers only the
M305.002 statement. The finite-group instance, Herbrand and inverse
functions, upper groups, host inertia and reciprocity conclusions remain
separate work.

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

Original copyright and authorship are retained: copyright 2026 Naganori
Yamaguchi, all rights reserved; authors Naganori Yamaguchi (assisted by
OpenAI Codex). Apache-2.0 applies. The existing verbatim
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged,
including inherited third-party notices. Their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

Worker 106 contributed the source extraction, exact telescope, closed
statement design and statement/proof phase boundary. Worker 1199
independently read the original and published interfaces, implemented the
closed target and wrote this companion on 1 November 2026. The Lean
header records the modifications. The approved environment is Lean 4.34.0
with Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`, distinct
from upstream's Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
