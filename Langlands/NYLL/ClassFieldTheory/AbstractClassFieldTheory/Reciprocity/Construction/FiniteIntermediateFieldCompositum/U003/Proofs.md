# A common finite stage below finitely many finite stages

This module proves the theorem
`Langlands.NYLL.ClassFormation.FiniteIntermediateField.exists_common_compositum`, the proof phase of
M037.003 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m037).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.FiniteIntermediateField.exists_common_compositumStatement` applied to the
theorem's parameters:

```lean
theorem exists_common_compositum {E K : ClosedSubgroup G} {ι : Type v}
    (M : FiniteIntermediateField E K) (s : Finset ι)
    (F : ι → FiniteIntermediateField E K) :
    exists_common_compositumStatement M s F
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : Type u} [Group G] [TopologicalSpace G]` in `section finiteIntermediateFields`, `namespace FiniteIntermediateField`, with `universe u v`. The theorem takes `{E K : ClosedSubgroup G} {ι : Type v}`, `M`, `s` and `F`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateFieldCompositum.Statements`, the target is the proposition

```lean
∃ P : FiniteIntermediateField E K,
  P.field.toSubgroup ≤ M.field.toSubgroup ∧
    ∀ i ∈ s, P.field.toSubgroup ≤ (F i).field.toSubgroup
```

Here `E K : ClosedSubgroup G` are closed subgroups of the topological group `G`, viewed as abstract fields, and `FiniteIntermediateField E K` (M029.001) is the type of closed subgroups `field` with `E ≤ field ≤ K` and finite index of `field` in `K` (a finite intermediate field of `E / K` in the abstract Galois correspondence, where smaller subgroups are larger fields). For `M`, a finite set `s` of indices and a family `F` of such stages, the target asserts a finite stage `P` whose subgroup is contained in that of `M` and of every `F i` with `i ∈ s`, i.e. a common finite overfield of `M` and the `F i`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateFieldCompositum.Statements`, which defines the target and imports `FiniteIntermediateField` (M029.001);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateCompositum.Compositum.Definitions`, the published definition of `FiniteIntermediateField.compositum` (M034.001), whose `field` is `M.field ⊓ N.field`.

The module opens no namespace; the source's `open KummerTheory`, `open CyclicCohomology`, `open CategoryTheory` and `open scoped BigOperators` are not needed, since none of their names or notation occur in the proof.

## Implemented proof

After `show` states the published proposition unfolded, the proof states the two bounds of the compositum as local facts: `hleft P N : (P.compositum N).field.toSubgroup ≤ P.field.toSubgroup` is `inf_le_left` and `hright P N : (P.compositum N).field.toSubgroup ≤ N.field.toSubgroup` is `inf_le_right`, since the field of `P.compositum N` is `P.field ⊓ N.field`. These are the source proofs of M034.002 `compositum_le_left` and M034.003 `compositum_le_right`, whose statements are published but whose proofs are not yet in the Library. The rest is the source proof with `hleft` and `hright` in place of those two theorems: after `classical`, induction on the finite set `s` with `Finset.induction_on`. For `s = ∅`, `M` itself works (`le_rfl`, and the second condition is vacuous by `Finset.notMem_empty`). For `insert i s`, the induction hypothesis gives `P` below `M` and all `F j`, `j ∈ s`; then `Q := P.compositum (F i)` is below `M` by `(hleft P (F i)).trans hPM`, below `F i` by `hright P (F i)` (after `simpa [hji]` for `j = i`), and below `F j` for `j ∈ s` by `(hleft P (F i)).trans (hPF j hj)`.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateFieldCompositum.lean`, lines 54–75](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateFieldCompositum.lean#L54-L75):
the docstring at lines 54–56 and the theorem at lines 57–75. It lies in `universe u v` (line 16), `namespace ClassFormation` (line 18) with `open KummerTheory` (line 20) and `open CyclicCohomology` (line 21), its `noncomputable section` (line 25) with `open CategoryTheory` (line 27) and `open scoped BigOperators` (line 28), `section finiteIntermediateFields` (line 30) with `variable {G : Type u} [Group G] [TopologicalSpace G]` (line 32) and `namespace FiniteIntermediateField` (line 34). The source is:

```lean
/-- An initial finite stage and finitely many further stages have a common
finite overfield.  This existential form avoids choosing an artificial
ordering of the finite family. -/
theorem exists_common_compositum {E K : ClosedSubgroup G} {ι : Type v}
    (M : FiniteIntermediateField E K) (s : Finset ι)
    (F : ι → FiniteIntermediateField E K) :
    ∃ P : FiniteIntermediateField E K,
      P.field.toSubgroup ≤ M.field.toSubgroup ∧
        ∀ i ∈ s, P.field.toSubgroup ≤ (F i).field.toSubgroup := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨M, le_rfl, fun i hi => (Finset.notMem_empty i hi).elim⟩
  | @insert i s hi ih =>
      rcases ih with ⟨P, hPM, hPF⟩
      let Q := P.compositum (F i)
      refine ⟨Q, (P.compositum_le_left (F i)).trans hPM, ?_⟩
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with hji | hj
      · simpa [hji] using P.compositum_le_right (F i)
      · exact (P.compositum_le_left (F i)).trans (hPF j hj)
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateFieldCompositum.lean`;
its SHA-256 is `924ba9423c5c9c4fc389345e02f552dc93d98f2c87114448f72f841a0085e2ec`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `exists_common_compositumStatement M s F` as its type, and begin the proof with `show` stating it unfolded;
- state the source proofs `inf_le_left` and `inf_le_right` of M034.002 `compositum_le_left` and M034.003 `compositum_le_right` as the local facts `hleft` and `hright` (before `classical`), and use them in place of `P.compositum_le_left (F i)` and `P.compositum_le_right (F i)`;
- omit the source's unused `open` commands and all other source declarations.

The theorem's name, docstring, binders and the remaining proof steps are the source's. The retained original belongs to registered source
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

This module proves only M037.003. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
