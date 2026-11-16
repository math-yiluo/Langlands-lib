# NYLL M029.022, M029.023: targets for the subgroup of the maximal unramified field inside `G_K`

The paired Lean file adapts the statements of two theorems of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`.
The pinned source file has SHA-256
`7d4c7c59cd25c27a728b49b8b4df61649bc818d2ef7ff4fdc375a92ea13f7460`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ClassFormation.DegreeData.` |
| --- | --- | --- | --- | --- | --- |
| M029.022 | `extensionSubgroup_maximalUnramifiedField` | 249–250 | 251–255 | 256–270 | `extensionSubgroup_maximalUnramifiedFieldStatement` |
| M029.023 | `extensionSubgroup_maximalUnramifiedField_normal` | 272 | 273–277 | 278–279 | `extensionSubgroup_maximalUnramifiedField_normalStatement` |

The source file imports `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements`
and `Nyll.GaloisCohomology.Cyclic.IntegralRepUniverse` (lines 7–8). The
context of the two theorems is `universe u` (line 18),
`namespace ClassFormation` (line 20), `open KummerTheory` (line 22),
`open CyclicCohomology` (line 24), `noncomputable section` (line 28), the
section `maximalUnramifiedFields` (lines 198 and 283) with its variable line
200,

```lean
variable {G : Type u} [Group G] [TopologicalSpace G]
```

`namespace DegreeData` (lines 202 and 281), and the closing lines 419–420.
The port keeps this context in the same order and omits `open KummerTheory`,
which neither target uses.

The names used in the statements resolve to published `Langlands.NYLL`
declarations: `ClassFormation.DegreeData` (M010.002, in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`), the maximal unramified field
`ClassFormation.DegreeData.maximalUnramifiedField` (M029.016, in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions`), the relative
inertia subgroup `ClassFormation.DegreeData.extensionInertiaWithin K L hLK`,
which is `L.toSubgroup.subgroupOf K.toSubgroup ⊓ D.fieldInertiaWithin K`
(M012.002, in `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Definitions`), and the relative
subgroup `CyclicCohomology.extensionSubgroup K L hLK`, which is
`L.toSubgroup.subgroupOf K.toSubgroup` (M004.002, in
`Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`,
found through `open CyclicCohomology`). Mathlib supplies `ClosedSubgroup`,
`Subgroup`, `Subgroup.Normal` and the order on subgroups.

Both source statements mention the proof term
`D.maximalUnramifiedField_le_of_le hLK` of M029.020 (lines 234–237), the
containment `(D.maximalUnramifiedField L).toSubgroup ≤ K.toSubgroup`, as the
third argument of `extensionSubgroup`. Its source proof is
`(D.maximalUnramifiedField_le L).trans hLK`. Neither M029.020 nor M029.019
has a published proof, so the port writes the source proof of M029.020 in
place of the theorem, with M029.019 replaced as follows.

The source proof of M029.019
`DegreeData.maximalUnramifiedField_le` (`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`, docstring line 227,
theorem lines 228–231) is

```lean
theorem maximalUnramifiedField_le (D : DegreeData G) (L : ClosedSubgroup G) :
    (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup := by
  rw [D.maximalUnramifiedField_eq_fieldInertia]
  exact inf_le_left
```

where M029.017 `maximalUnramifiedField_eq_fieldInertia` (lines 213–216) is
the equation `D.maximalUnramifiedField L = D.fieldInertia L`, proved by
`rfl`. Neither proof is published. The published definitions make
`D.maximalUnramifiedField L` (M029.016) equal by definition to
`D.fieldInertia L` (M010.012), the closed subgroup `L ⊓ D.inertia`. The
port therefore writes the term

```lean
show (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup from
  inf_le_left
```

in place of `D.maximalUnramifiedField_le L`: `show` states the source
proposition of M029.019, and Lean checks `inf_le_left` against it by
definitional unfolding, which replaces the `rfl` rewrite. Mathlib supplies
`ClosedSubgroup`, its lattice structure and `inf_le_left`.

Because the replaced terms are proofs of the same propositions, proof
irrelevance makes the two targets definitionally equal to the source
statements. Moreover, the published `extensionSubgroup K E _hEK` is the
`abbrev` `E.toSubgroup.subgroupOf K.toSubgroup`, which does not use its
proof argument at all.

## Targets and complete telescopes

Both targets have the section binders implicit `{G : Type u}`, `[Group G]`
and `[TopologicalSpace G]`, followed by the binders shown, and each is a
`Prop`.

### M029.022

```lean
/-- The proposition, from the source theorem
`extensionSubgroup_maximalUnramifiedField`, that inside `G_K` the absolute
subgroup of the maximal unramified field `\widetilde L` is the relative
inertia subgroup. -/
def extensionSubgroup_maximalUnramifiedFieldStatement (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) : Prop :=
    extensionSubgroup K (D.maximalUnramifiedField L)
        ((show (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup from
          inf_le_left).trans hLK) =
      D.extensionInertiaWithin K L hLK
```

For closed subgroups `K` and `L` with `G_L ≤ G_K`, the subgroup of `G_K`
representing the maximal unramified field `\widetilde L`, that is,
`(L ⊓ D.inertia)` viewed inside `G_K`, equals the relative inertia subgroup
`(G_L inside G_K) ⊓ ker(d|G_K)`.

### M029.023

```lean
set_option linter.unusedVariables false in
/-- The proposition, from the source theorem
`extensionSubgroup_maximalUnramifiedField_normal`, that the subgroup
representing the maximal unramified field is normal in the base subgroup
when the subgroup of `L` is. -/
def extensionSubgroup_maximalUnramifiedField_normalStatement (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] : Prop :=
    (extensionSubgroup K (D.maximalUnramifiedField L)
      ((show (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup from
        inf_le_left).trans hLK)).Normal
```

If the subgroup representing `L` is normal in `G_K`, so is the subgroup
representing `\widetilde L`. The instance binder `hLnormal` is used only by
the source proof (through `infer_instance` after the rewrite with M029.022);
a prover of the target receives it as an instance.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the targets lie in
   `Langlands.NYLL.ClassFormation.DegreeData`.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The binders are copied
   verbatim, including names, kinds and order; `: Prop :=` is appended to
   the last telescope line. The source proofs are omitted: this contribution
   publishes the proposition targets, and their proofs are separate work.
3. In both statements replace the proof argument
   `(D.maximalUnramifiedField_le_of_le hLK)` by
   `((show (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup from inf_le_left).trans hLK)`,
   as explained above, with line breaks inside the term. The rest of each
   statement is verbatim.
4. Precede M029.023 by `set_option linter.unusedVariables false in`.
   Without it, Lean's unused-variables linter warns about `hLnormal`, which
   the proposition does not mention. The option affects only the linter and
   keeps the source binder name.
5. Replace each source docstring by a description of the proposition that
   names the source theorem, and the source module docstring by a
   description of this module with a modification notice.
6. Replace the two source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions` (which imports
   the modules of `DegreeData`, `fieldInertia` and `extensionSubgroup`) and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Definitions`.
7. Keep the source context listed above, without `open KummerTheory`; omit
   the other declarations of the source file. No helper declaration or
   instance is added.

These are the exact source statements as named propositions, without
published proofs; only proof arguments inside them are written out. They
discharge no host class-formation, Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), together with the other five
modules of this contribution, with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
