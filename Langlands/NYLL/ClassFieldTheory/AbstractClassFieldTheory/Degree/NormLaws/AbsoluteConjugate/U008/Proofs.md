# Absolute conjugation of a coset representative

This module proves the theorem
`Langlands.NYLL.ClassFormation.absoluteConjugateCosetEquiv_mk`, the proof phase of
M026.008 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m026).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.absoluteConjugateCosetEquiv_mkStatement` applied to the
theorem's parameters:

```lean
theorem absoluteConjugateCosetEquiv_mk
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G)
    (x : (baseField G).toSubgroup) :
    absoluteConjugateCosetEquiv_mkStatement K σ x
```

## Target and binders

The theorem has its own binders `{G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]`, `K`, `σ` and `x`, exactly as the published target and the source theorem; the module declares no section variables (the source's section variable `G` is not used by this theorem).

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.AbsoluteConjugate.Statements`, the target is the proposition

```lean
absoluteConjugateCosetEquiv K σ (QuotientGroup.mk x) =
  QuotientGroup.mk (Langlands.NYLL.PortInternal.M026.d005 σ x)
```

Here `G` is a topological group with continuous multiplication, `K : ClosedSubgroup G`, `σ : G` and `x` is an element of `(baseField G).toSubgroup`, the whole group `G` as the subgroup of the base field (M010.003). `Langlands.NYLL.PortInternal.M026.d005 σ` (M026.005, the private source definition `absoluteConjugationEquiv`) is the bijection `x ↦ σ x σ⁻¹` of that subgroup, and `absoluteConjugateCosetEquiv K σ` (M026.007) is the induced equivalence from the left cosets of `K^σ` (M026.001) to the left cosets of `K` in `G`. The target says that it sends the coset of `x` to the coset of `σ x σ⁻¹`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.AbsoluteConjugate.Statements`, which defines the target and imports `absoluteConjugateCosetEquiv` (M026.007) and `Langlands.NYLL.PortInternal.M026.d005` (M026.005).

The module opens no namespace; the source's `open KummerTheory`, `open CyclicCohomology` and `open scoped BigOperators Pointwise` are not needed, since none of their names or notation occur in the statement or the proof.

## Implemented proof

After `show` states the published proposition unfolded, the proof is the source proof `rfl`: by its definition (M026.007), `absoluteConjugateCosetEquiv K σ` is `Quotient.congr (Langlands.NYLL.PortInternal.M026.d005 σ) _`, which maps the class of `x` to the class of `Langlands.NYLL.PortInternal.M026.d005 σ x` by definition.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`, lines 132–143](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean#L132-L143):
the docstring at lines 132–135, the attribute at line 136 and the theorem at lines 137–143. It lies in `namespace ClassFormation` (line 16), with `open KummerTheory` (line 18) and `open CyclicCohomology` (line 20), its `noncomputable section` (line 24), `open scoped BigOperators Pointwise` (line 26) and the variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 29). The source is:

```lean
/--
Establishes the identity `absoluteConjugateCosetEquiv K σ (QuotientGroup.mk x) = QuotientGroup.mk
(absoluteConjugationEquiv σ x)`.
-/
@[simp]
theorem absoluteConjugateCosetEquiv_mk
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G)
    (x : (baseField G).toSubgroup) :
    absoluteConjugateCosetEquiv K σ (QuotientGroup.mk x) =
      QuotientGroup.mk (absoluteConjugationEquiv σ x) :=
  rfl
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`;
its SHA-256 is `985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `absoluteConjugateCosetEquiv_mkStatement K σ x` as its type, and begin the proof with `show` stating it unfolded; in it the private source definition `absoluteConjugationEquiv` (M026.005) is written by its published name `Langlands.NYLL.PortInternal.M026.d005`; the source's term proof `rfl` is kept as the tactic `rfl`;
- omit the `@[simp]` attribute (the theorem's type is the published `...Statement` proposition, not an equation), the source opens and section variables, and all other source declarations.

The theorem's name, docstring (which names `absoluteConjugationEquiv` as the source does) and binders are the source's. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. The unchanged
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M026.008. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
