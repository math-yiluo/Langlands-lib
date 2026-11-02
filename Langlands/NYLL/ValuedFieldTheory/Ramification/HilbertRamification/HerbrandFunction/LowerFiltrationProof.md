# Natural-level projection of the actual lower filtration: proof

The module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LowerFiltrationProof`
proves M305.002, using the reserved adapted source theorem name
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.lowerRamificationFiltrationOfUniqueExtension_lower`.
Its complete declaration type is exactly

```lean
Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.LowerRamificationFiltrationProjectionStatement.{u, v, w, x}
```

The four universes are independent. There are no mathematical parameters
or premises outside this published closed proposition. The module imports
only the published
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LowerFiltrationStatement`;
that statement, the actual construction and all their imported
Lean/Markdown pairs are reused unchanged.

## Scope and implemented proof

Inside its body the target quantifies implicit fields `K : Type u` and
`L : Type w`, supplied `Field K`, `Field L` and `Algebra K L`, implicit
`base : DVF.{u,v} K` and `target : DVF.{w,x} L`, the supplied instance
`base.valuation.HasExtension target.valuation`, explicit
`huniq : HasUniqueValuationExtension.{u,v,w,x,x} base target`, and every
explicit natural index `n`. Here `DVF` is in
`Langlands.NYLL.ValuationTheory.DiscreteValuationField` and the uniqueness
predicate is in
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF`.
The comparison-valuation universe remains `x`.

For those same supplied data, the equality is

```lean
(lowerRamificationFiltrationOfUniqueExtension
  (base := base) (target := target) huniq).lower n =
  lowerRamificationGroup
    (base := base) (target := target) huniq (n : ℝ)
```

Both sides are actual subgroups of Mathlib's `Gal(L/K) = L ≃ₐ[K] L`.
The canonical natural-to-real cast is unchanged, and `n = 0` is included.
The proof does not require finite dimensionality, a finite group,
completeness, `IsGalois`, residue separability or additional filtration
laws. Normality and antitonicity are already proved fields of the actual
construction.

The complete implemented proof is:

```lean
intro K L instK instL instAlg base target instExt huniq n
rfl
```

`intro` unfolds the closed proposition as needed and introduces all ten
binders, including the supplied field, algebra and extension instances.
The actual construction defines its `lower` field by
`lower n := lowerRamificationGroup (base := base) (target := target) huniq (n : ℝ)`.
Reducing that definition and projecting the field makes the two sides
identical; `rfl` supplies reflexivity. The stored normality and
antitonicity proofs impose no further proof obligation here. No transport,
replacement filtration or separate membership argument is involved.
The source's `@[simp]` attribute is retained on the theorem of the closed
target.

## Source correspondence and modifications

The original is Naganori Yamaguchi's *ClassFieldTheory (NYLL)* at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/HerbrandFunction.lean`, lines 32–63](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/HerbrandFunction.lean#L32-L63).
The complete file has SHA-256
`a094355ce3645fe924eb8575233a874ca16007f91ab9bafe99f13c33cd3a878c`.
Original lines 1–100 were read directly. The shared telescope is at
32–35, actual construction at 40–52, projection documentation at 54,
theorem and signature at 55–62, and original `rfl` proof at 63.
The finite-dimensional assumption starts only at 65, after this theorem.

The namespace gains `Langlands.NYLL`, and the single focused published
statement import replaces the original whole-module imports. The original
theorem name, equality, natural-to-real cast and `rfl` argument are
retained. The only proof adaptation is introducing the telescope that
the published statement places inside a closed `Prop`. This internal
universal closure is the published organizational adaptation of the
source signature. The unused namespace opening and noncomputable section
are unnecessary for this proof and are omitted. The Lean header records
these modifications.

The public partition
`notes/reuse/nyll-public-port/m289-m312.md` identifies M305.002 at original
line 55 and records no patch10 change for the source module. Its
conservative source-order edges are scheduling information. This proof
establishes exactly the natural-level projection. Later finite-group,
Herbrand, inverse, upper-group, host inertia and reciprocity units remain
separate.

## Attribution and environment

The registered source is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the original
path above. The attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No workspace, project or supplied-Library `notes/errata` directory was
present at preparation.

Original copyright and authorship are retained: copyright 2026 Naganori
Yamaguchi, all rights reserved; authors Naganori Yamaguchi (assisted by
OpenAI Codex). Apache-2.0 applies. The existing verbatim
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE), including inherited
third-party notices, are reused unchanged. Their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

Worker 106 contributed the reused source extraction, exact telescope
analysis and proof routing. Worker 60 independently checked the original
and published interfaces, implemented the closed-target proof and wrote
this companion on 1 November 2026. Worker 1199's published closed target
and actual construction are imported unchanged.

The approved environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, distinct from upstream's
Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
