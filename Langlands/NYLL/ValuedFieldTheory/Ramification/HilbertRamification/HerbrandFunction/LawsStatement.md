# Actual unique-extension Herbrand laws: statement

This module defines one closed proposition,
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.UniqueExtensionHerbrandLawsStatement`,
in module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LawsStatement`.
It packages the eight conclusions M305.006–.011/.013–.014 from Naganori
Yamaguchi's *ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/HerbrandFunction.lean`, lines 88–191](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/HerbrandFunction.lean#L88-L191).
The complete original file, including its supplied-data telescope,
finite-dimensional section and local automorphism-group instance, was read.
Its SHA-256 is
`a094355ce3645fe924eb8575233a874ca16007f91ab9bafe99f13c33cd3a878c`.

This contribution supplies a statement target. It contains no proof of this
proposition or of its individual laws. The original theorem names and
attributes remain available for separate proof work.

## Entire closed proposition

Inside namespace
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`, with four
independent universe levels `u v w x`, the entire definition is:

```lean
def UniqueExtensionHerbrandLawsStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target),
    (∀ s : ℝ,
      herbrandFunctionOfUniqueExtension (base := base) (target := target) huniq s =
        Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
          (lowerRamificationFiltrationOfUniqueExtension
            (base := base) (target := target) huniq) s) ∧
    (∀ t : ℝ,
      inverseHerbrandFunctionOfUniqueExtension (base := base) (target := target) huniq t =
        Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction
          (lowerRamificationFiltrationOfUniqueExtension
            (base := base) (target := target) huniq) t) ∧
    (∀ [FiniteDimensional K L],
      (∀ t : ℝ,
        herbrandFunctionOfUniqueExtension (base := base) (target := target) huniq
          (inverseHerbrandFunctionOfUniqueExtension
            (base := base) (target := target) huniq t) = t) ∧
      (∀ s : ℝ,
        inverseHerbrandFunctionOfUniqueExtension (base := base) (target := target) huniq
          (herbrandFunctionOfUniqueExtension
            (base := base) (target := target) huniq s) = s) ∧
      StrictMono (herbrandFunctionOfUniqueExtension (base := base) (target := target) huniq) ∧
      StrictMono (inverseHerbrandFunctionOfUniqueExtension (base := base) (target := target) huniq) ∧
      (∀ s : ℝ,
        upperRamificationGroupOfUniqueExtension (base := base) (target := target) huniq
          (herbrandFunctionOfUniqueExtension
            (base := base) (target := target) huniq s) =
          lowerRamificationGroup (base := base) (target := target) huniq s) ∧
      (∀ t : ℝ,
        (-1 : ℝ) ≤ inverseHerbrandFunctionOfUniqueExtension
          (base := base) (target := target) huniq t ↔ (-1 : ℝ) ≤ t))

```

The unapplied constant has type `Prop`. Every term binder occurs inside
its defining proposition: implicit fields `K : Type u`, `L : Type w`,
supplied field structures and `Algebra K L`, implicit supplied DVFs
`base : DVF.{u,v} K` and `target : DVF.{w,x} L`, the supplied
`base.valuation.HasExtension target.valuation` instance, and explicit
`huniq : HasUniqueValuationExtension.{u,v,w,x,x} base target`.
The comparison valuation universe is `x`, as in the source. The field
universes `u,w` and value-group universes `v,x` are independent; no two
levels are identified. There are no external term parameters.

## Two scope blocks and the actual objects

For fixed supplied data and `huniq`, the proposition has the shape
`evaluation1 ∧ evaluation2 ∧ (∀ [FiniteDimensional K L], sixLaws)`.
The first scope block consists of the two unrestricted evaluation clauses.
They identify the actual forward and inverse wrappers with the published
generic functions evaluated on
`lowerRamificationFiltrationOfUniqueExtension (base := base) (target := target) huniq`.
The original signatures explicitly use `omit [FiniteDimensional K L]`
at lines 88 and 100. Although they occur after the source section's
finite-dimensional variable, that hypothesis is absent from these two
signatures. The target retains their unrestricted scope.

The second block quantifies internally over a supplied
`[FiniteDimensional K L]` before the ordered conjunction of six laws:
forward-after-inverse, inverse-after-forward, strict monotonicity of the
forward function, strict monotonicity of the inverse function, evaluation
of the actual upper group at the forward index, and preservation of the
lower bound `-1` by the inverse function. Each real variable is quantified
inside its own clause. Strict monotonicity is on the full real line.
The last biconditional is the exact source lower-bound assertion.

Every expression passes the identical `base`, `target` and `huniq`.
The lower filtration is the published actual filtration; its natural
level `n` is the actual `lowerRamificationGroup huniq (n : ℝ)`.
The published upper group evaluates that actual real lower-group family
at `inverseHerbrandFunctionOfUniqueExtension huniq t`.
Thus clause 7 is an equality in `Subgroup Gal(L/K)`, where Mathlib's
`Gal(L/K)` is the actual algebra automorphism group `L ≃ₐ[K] L` under
composition. No abstract replacement group or subgroup occurs.

The proposition adds no completeness, residue-separability, `IsGalois`,
eventual-triviality or inverse-law premise, and assumes none of its
conclusions. In particular, the generic inverse is the previously
published `Function.invFun` construction; its existence as data does not
supply the inverse laws asserted here. The finite-dimensional block
retains the source scope for those laws, while the existing data
constructors and two evaluation clauses remain unrestricted.
The source `generalDVFGalFintype` local instance is not installed or
redeclared. No new instance is needed to form this proposition.

## Complete eight-row original-to-adapted correspondence

All original names in this table belong to
`RamificationTheory.HilbertRamification.Higher`.
The adapted destination for every row is the indicated clause of the
single closed declaration
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.UniqueExtensionHerbrandLawsStatement`.
The rows record the complete selected source interval, including the
adjacent scope/docstring lines where present. The definitions between
these source theorems are already published and are imported unchanged.

| Source unit and lines | Original declaration in the namespace above | Adapted destination and exact content | Scope |
| --- | --- | --- | --- |
| M305.006, 88–98 | `herbrandFunctionOfUniqueExtension_apply` | Clause 1, forward wrapper equals generic `herbrandFunction` on the actual lower filtration, for every `s : ℝ` | Supplied data only; original explicit `omit` |
| M305.007, 100–110 | `inverseHerbrandFunctionOfUniqueExtension_apply` | Clause 2, inverse wrapper equals generic `inverseHerbrandFunction` on that same filtration, for every `t : ℝ` | Supplied data only; original explicit `omit` |
| M305.008, 112–122 | `herbrandFunctionOfUniqueExtension_psi` | Clause 3, forward function after inverse function equals `t`, for every `t : ℝ` | Internal `FiniteDimensional K L` block |
| M305.009, 124–134 | `inverseHerbrandFunctionOfUniqueExtension_eta` | Clause 4, inverse function after forward function equals `s`, for every `s : ℝ` | Internal `FiniteDimensional K L` block |
| M305.010, 136–144 | `herbrandFunctionOfUniqueExtension_strictMono` | Clause 5, `StrictMono` of the actual forward function | Internal `FiniteDimensional K L` block |
| M305.011, 146–154 | `inverseHerbrandFunctionOfUniqueExtension_strictMono` | Clause 6, `StrictMono` of the actual inverse function | Internal `FiniteDimensional K L` block |
| M305.013, 166–178 | `upperRamificationGroupOfUniqueExtension_herbrandFunction` | Clause 7, actual upper group at the forward index equals the actual lower group at `s`, for every `s : ℝ` | Internal `FiniteDimensional K L` block |
| M305.014, 180–191 | `inverseHerbrandFunctionOfUniqueExtension_ge_neg_one_iff` | Clause 8, `-1 ≤ inverseHerbrandFunctionOfUniqueExtension huniq t ↔ -1 ≤ t`, for every `t : ℝ` | Internal `FiniteDimensional K L` block |

These are eight theorem conclusions aggregated into a proposition;
no original theorem body is copied into this module. Original explicit
`s` and `t` parameters become clause-local universal quantifiers. The
last source theorem's implicit `{t : ℝ}` is likewise universally
quantified inside clause 8. Original source order is preserved.

## Extraction, imports and dependency boundary

The namespace gains the prefix `Langlands.NYLL`. Generic function and
DVF names are qualified under that prefix, and every actual wrapper
application explicitly supplies the original valuations. All ambient
supplied-data parameters move inside the `Prop` body. The original
finite-dimensional section is represented by the internal binder
before clauses 3–8. No unused opening, `noncomputable section`, proof,
`@[simp]` attribute or local source instance is copied. Forming this
proposition requires no noncomputable definition modifier.

The original wholesale imports of `Herbrand.Function` and
`HilbertRamification.RealLowerGroups` are replaced by the one focused
published module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.Definitions`.
It supplies the actual forward/inverse wrappers and upper group, and
imports the published generic inverse and actual lower filtration.
The corresponding
[actual definitions](Definitions.md),
[lower filtration](LowerFiltration.md), and
[generic inverse](../../Herbrand/Function/InverseDefinition.md)
are reused unchanged, together with their dependencies and paired
Markdown. No proof module for the generic inverse laws is imported.

The public [M305 partition](../../../../../../notes/reuse/nyll-public-port/m289-m312.md#m305)
records no patch10 change for this source. Its source-order and
module-completion edges are scheduling guidance; they add no premises
to the proposition. The generic inverse context at original
`Herbrand/Function.lean` lines 1–70 and 335–408 was also read; that
whole file has SHA-256
`668006f8122da36b9bd34657988f9d0d6164a629ea10feb340002f2317c40580`.
Its finite-group inverse and order proofs explain the later proof route,
but are unnecessary to state this target. Neither its
`herbrandOrderIso` nor the host `Langlands.Ramification.Padic.herbrandPsi`
is used. The latter has a different arithmetic/cutoff construction.

This unit adds only the closed eight-clause target. Generic inverse
proofs, proofs of this actual target, filtered reciprocity, host inertia
and the parent reciprocity objectives are separate work.

## Sources, license, authorship and environment

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the
original path above. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No workspace, project or supplied-Library `notes/errata` directory
was present when checked on 2 November 2026.

The original header is retained verbatim: copyright 2026 Naganori
Yamaguchi, all rights reserved; authors Naganori Yamaguchi (assisted by
OpenAI Codex). Apache-2.0 applies. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) match the pinned originals,
with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
All inherited notices are preserved; the root NOTICE inventory has no
entry for this source file. The Lean header explicitly records the
extraction and namespace, import and scope changes.

Worker 106 contributed the source/interface analysis and closed-target
design recorded in the task. Worker 27 checked the original and
published interfaces, implemented this target and wrote its companion.
Existing published definitions by Worker 1199 are imported unchanged.
The approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, rather than upstream
Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
