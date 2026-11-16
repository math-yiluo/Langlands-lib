# Conjugation preserves inclusions of abstract fields

This module proves the theorem
`Langlands.NYLL.ClassFormation.conjugateClosedSubgroup_mono`, the proof phase of
M035.001 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m035).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.conjugateClosedSubgroup_monoStatement` applied to the
theorem's parameters:

```lean
theorem conjugateClosedSubgroup_mono [ContinuousMul G]
    {K L : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup)
    (s : G) :
    conjugateClosedSubgroup_monoStatement hLK s
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : Type u} [Group G] [TopologicalSpace G]`, in `section GroupOnly`. The theorem takes the instance `[ContinuousMul G]`, `{K L}`, `hLK` and `s`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormConjugation.Mono.Statements`, the target is the proposition

```lean
(conjugateClosedSubgroup L s).toSubgroup ≤
  (conjugateClosedSubgroup K s).toSubgroup
```

Here `K L : ClosedSubgroup G` with `hLK : L.toSubgroup ≤ K.toSubgroup`, `s : G`, and `conjugateClosedSubgroup K s` (M026.001) is the closed subgroup with underlying subgroup `ConjAct.toConjAct s⁻¹ • K.toSubgroup`, that is `s⁻¹ G_K s`, the subgroup of the right conjugate field `K^s`. The target says that conjugation by `s` preserves the inclusion `G_L ≤ G_K`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormConjugation.Mono.Statements`, which defines the target and imports `conjugateClosedSubgroup` (M026.001);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs`, the published proof of M026.002 `conjugateClosedSubgroup_mem`, of type `conjugateClosedSubgroup_memStatement K σ x`, which unfolds to `x ∈ conjugateClosedSubgroup K σ ↔ σ * x * σ⁻¹ ∈ K`.

The module opens no namespace; the source's `open KummerTheory`, `open CyclicCohomology` and `open scoped BigOperators` are not needed.

## Implemented proof

After `show` states the published proposition unfolded, the proof is the source proof: it takes `x` in the left subgroup and uses `change` to state membership in the closed subgroups. The source then rewrites both memberships with `conjugateClosedSubgroup_mem` and applies `hLK`; since the published M026.002 result has a `...Statement` type, the port instead applies its `.mp` to `hx` (giving `s * x * s⁻¹ ∈ L`), then `hLK`, then its `.mpr` for `K`.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormConjugation.lean`, lines 36–46](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormConjugation.lean#L36-L46):
the docstring at line 36 and the theorem at lines 37–46. It lies in `namespace ClassFormation` (line 18), with `open KummerTheory` (line 20), `open CyclicCohomology` (line 22), its `noncomputable section` (line 26), `open scoped BigOperators` (line 28), `universe u` (line 30), `section GroupOnly` (line 32) and the variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 34). The source is:

```lean
/-- Conjugation preserves inclusions of abstract fields. -/
theorem conjugateClosedSubgroup_mono [ContinuousMul G]
    {K L : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup)
    (s : G) :
    (conjugateClosedSubgroup L s).toSubgroup ≤
      (conjugateClosedSubgroup K s).toSubgroup := by
  intro x hx
  change x ∈ conjugateClosedSubgroup L s at hx
  change x ∈ conjugateClosedSubgroup K s
  rw [conjugateClosedSubgroup_mem] at hx ⊢
  exact hLK hx
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormConjugation.lean`;
its SHA-256 is `2ec220a4a18e54914548db7f0ecea669819fe5b6f8b421c13e996dd6ceed4602`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `conjugateClosedSubgroup_monoStatement hLK s` as its type, and begin the proof with `show` stating it unfolded;
- replace the source's `rw [conjugateClosedSubgroup_mem] at hx ⊢` and `exact hLK hx` by the term `(conjugateClosedSubgroup_mem K s x).mpr (hLK ((conjugateClosedSubgroup_mem L s x).mp hx))`, because the published M026.002 result has a `...Statement` type;
- omit `open KummerTheory`, `open CyclicCohomology`, `open scoped BigOperators` and all other source declarations.

The theorem's name, docstring, binders and its first proof steps are the source's. The retained original belongs to registered source
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

This module proves only M035.001. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
