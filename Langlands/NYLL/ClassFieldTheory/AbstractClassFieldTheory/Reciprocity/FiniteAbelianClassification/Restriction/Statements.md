# NYLL M298.010 and M298.017: restriction targets

Worker 458, 14 November 2026.

## Source

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean`
(file SHA-256
`0bc99c03d0936ca803d6497174ef17999b76789381f183f525a9f098eac7fd83`), lines
248–259 (M298.010) and 377–414 (M298.017), with the scaffolding at lines
23–34. Registered source `external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`), content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Name map

Original names have the prefix `ClassFormation.FiniteAbelianSubextension.`,
adapted names the prefix `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.`.
Line ranges include the docstring and attributes.

| Unit | Original theorem | Source lines | Adapted target |
| --- | --- | --- | --- |
| M298.010 | `restriction_mk` | 248–259 (theorem at 252) | `restriction_mkStatement` |
| M298.017 | `eq_of_le_of_extensionQuotient_card_eq` | 377–414 (theorem at 382) | `eq_of_le_of_extensionQuotient_card_eqStatement` |

Each target is a `def` whose type is `Prop`. Its binders are exactly the
source theorem's binders, hypotheses included, in the same order and with the
same binder kinds, and its body is exactly the source theorem's conclusion.
So proving the source theorem for given arguments is the same as proving the
target applied to them. No proof is given here.

## The targets

Both targets have the source telescope: implicit `{G : Type*}` (a
universe-polymorphic type, the single universe parameter `u_1`), instance
arguments `[Group G] [TopologicalSpace G]`, implicit
`{K : ClosedSubgroup G}`, implicit `{L₁ L₂ : FiniteAbelianSubextension K}`
and explicit `(h₁₂ : L₁ ≤ L₂)`. No `IsTopologicalGroup G` or class-formation
hypothesis is added. `L₁ ≤ L₂` is the M296.014 order: field inclusion
`L₁ ⊆ L₂`, by definition `L₂.field.toSubgroup ≤ L₁.field.toSubgroup`.

- **`restriction_mkStatement`** (M298.010) has the further explicit binder
  `(k : K.toSubgroup)` and body

  ```lean
  restriction h₁₂ (L₂.extensionQuotientMk k) =
    L₁.extensionQuotientMk k
  ```

  Restriction from `G(L₂/K)` to `G(L₁/K)` sends the class of `k ∈ G_K` to
  the class of `k`. Here `restriction` is the M298.009 definition
  `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.restriction` and
  `extensionQuotientMk` is the published quotient projection
  `G_K →* L.extensionQuotient` (M296.010).
- **`eq_of_le_of_extensionQuotient_card_eqStatement`** (M298.017) has the
  further explicit binder
  `(hcard : Nat.card L₂.extensionQuotient = Nat.card L₁.extensionQuotient)`
  and body `L₁ = L₂`. If `L₁ ⊆ L₂` and the actual Galois quotients
  `G(L₂/K)` and `G(L₁/K)` have the same cardinality, then the two finite
  abelian subextensions are equal. `Nat.card` is Mathlib's cardinality; both
  quotients are finite by the published instance M296.008.

In M298.017 the conclusion does not mention `h₁₂` or `hcard`; they are kept
as hypotheses of the target, as in the source, and
`set_option linter.unusedVariables false in` silences the linter for that
definition only.

## Reused Library declarations

- `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.restriction`
  (M298.009), and through it the local instances
  `Langlands.NYLL.PortInternal.M298.d001` and `d002`, from the sibling
  modules `FiniteAbelianClassification/Restriction/Definitions` and
  `FiniteAbelianClassification/QuotientInstances/Definitions`.
- `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension` with
  `extensionQuotient` and `extensionQuotientMk` (M296.001, .006, .010).
- The order instance `Langlands.NYLL.PortInternal.M296.d014` (M296.014).

## Instance scope

In the source, the local instances M298.001 and M298.002 (lines 36–46) are in
force throughout `namespace FiniteAbelianSubextension` (closed at line 516),
so they are in scope at both theorems. The module therefore runs
`attribute [local instance] Langlands.NYLL.PortInternal.M298.d001
Langlands.NYLL.PortInternal.M298.d002` inside its
`namespace FiniteAbelianSubextension`. The attribute is local and not
exported, so no global instance is added.

## Source scaffolding

Lines 23–34 of the source are `noncomputable section`,
`namespace ClassFormation`, `open CyclicCohomology KummerTheory`, the
variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 30),
`namespace FiniteAbelianSubextension` and `variable {K : ClosedSubgroup G}`
(line 34). Both theorems bind their own `{G : Type*}`, `[Group G]`,
`[TopologicalSpace G]` and `{K : ClosedSubgroup G}`, which shadow the section
variables, so the section variables do not enter their telescopes in the
source.

## Modifications

Worker 458 made only these changes:

1. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
2. Each theorem becomes a Prop-valued `def` named by appending `Statement` to
   its name, with the theorem's binders as the definition's binders and the
   theorem's conclusion as its body. The proofs (source lines 258–259 and
   388–414) are dropped.
3. The `@[simp]` attribute of `restriction_mk` (line 251) is dropped: it
   belongs to the theorem, not to a proposition definition.
4. The source docstrings are replaced by target docstrings that paraphrase
   them.
5. `set_option linter.unusedVariables false in` is added before the M298.017
   target (see above).
6. The section variables of source lines 30 and 34 are omitted (they enter no
   telescope), `open KummerTheory` is omitted (unused) and
   `open CyclicCohomology` is kept.
7. The two source local instances are installed with
   `attribute [local instance]`, as described above.
8. The source imports are replaced by the single published import these
   statements use, the sibling module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification.Restriction.Definitions`.

Binders, binder kinds, universes and conclusions are otherwise unchanged. A
focused `lean_check` of this module reports no errors or warnings, and
inspection of both targets reports `statement_returns_prop: true`.

## Scope

These are proposition targets only; their proofs are routed separately. The
source proof of M298.017 uses M298.010 and the surjectivity of
`abstractReciprocityRestriction`, not class-field existence. No reciprocity
or class-formation statement is asserted here.

## Licence

The original copyright, Apache-2.0 release and author header are kept at the
top of the Lean file, followed by a modification notice. The retained files
are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
