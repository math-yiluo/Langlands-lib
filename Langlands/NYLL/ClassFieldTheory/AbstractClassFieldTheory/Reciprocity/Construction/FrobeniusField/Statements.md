# NYLL M016.002, M016.003, M016.005–M016.010 and M016.012–M016.014: targets about the field fixed by a Frobenius lift

The paired Lean file adapts the statements of eleven theorems from Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean`.
The pinned source file has SHA-256
`707b3783859e0c991b0a4e5a3a5c014c808617f79587d1895e49787a26d1ca10`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M016.002 | `mem_frobeniusFixedSubgroupWithin_iff` (`@[simp]`, line 41) | 39–40 | 42–50 | 51 | `Langlands.NYLL.ClassFormation.DegreeData.mem_frobeniusFixedSubgroupWithin_iffStatement` |
| M016.003 | `frobeniusFixedSubgroupWithin_isClosed` | 53 | 54–61 | 62–67 | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedSubgroupWithin_isClosedStatement` |
| M016.005 | `mem_frobeniusFixedField_iff` (`@[simp]`, line 88) | 87 | 89–97 | 98 | `Langlands.NYLL.ClassFormation.DegreeData.mem_frobeniusFixedField_iffStatement` |
| M016.006 | `frobeniusFixedField_le` | 100 | 101–106 | 107–108 | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedField_leStatement` |
| M016.007 | `extensionSubgroup_frobeniusFixedField` | 110–111 | 112–120 | 121–133 | `Langlands.NYLL.ClassFormation.DegreeData.extensionSubgroup_frobeniusFixedFieldStatement` |
| M016.008 | `extensionInertiaWithin_le_frobeniusFixedSubgroupWithin` | 135 | 136–143 | 144–148 | `Langlands.NYLL.ClassFormation.DegreeData.extensionInertiaWithin_le_frobeniusFixedSubgroupWithinStatement` |
| M016.009 | `fieldInertia_le_frobeniusFixedField` | 150 | 151–158 | 159–166 | `Langlands.NYLL.ClassFormation.DegreeData.fieldInertia_le_frobeniusFixedFieldStatement` |
| M016.010 | `frobeniusFixedField_finite` | 168 | 169–179 | 180–200 | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedField_finiteStatement` |
| M016.012 | `frobeniusFixedField_index_le_extensionIndex_of_exponent_eq_one` | 216–217 | 218–230 | 231–243 | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedField_index_le_extensionIndex_of_exponent_eq_oneStatement` |
| M016.013 | `frobeniusFixedSubgroupWithin_inf_fieldInertiaWithin` | 245–247 | 248–258 | 259–288 | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedSubgroupWithin_inf_fieldInertiaWithinStatement` |
| M016.014 | `frobeniusFixedField_fieldInertia` | 290–291 | 292–300 | 301–322 | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedField_fieldInertiaStatement` |

The enclosing source context is `namespace ClassFormation` (line 17),
`open CyclicCohomology` (line 19), `noncomputable section` (line 23), the
variables at line 25 and `namespace DegreeData` (line 27). The source file
has no universe declaration.

The names used in the statements resolve to published `Langlands.NYLL`
declarations: `DegreeData.frobeniusFixedSubgroupWithin` and
`DegreeData.frobeniusFixedField` (M016.001 and M016.004, from the sibling
module `FrobeniusField.Definitions`), `DegreeData.frobeniusExponent` and
`DegreeData.frobeniusClosure` (M014.012 and M014.023, from
`Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`, submitted
together with this module), `DegreeData.FrobeniusElements` (M012.009),
`DegreeData.extensionInertiaWithin` (M012.002) with its normality instance
(M012.003), `DegreeData.fieldInertia` (M010.012; `D.fieldInertia L` is the
closed subgroup `L ⊓ D.inertia` of `G`, with `D.inertia` M010.006),
`DegreeData.fieldInertiaWithin` (M010.014; the kernel of the degree on
`G_K`, a subgroup of `G_K`), `DegreeData.FiniteResidueAbstractField`
(M010.021) and `DegreeData` (M010.002). `ClosedSubgroup`, `Subgroup`
membership, order and infimum, `Subgroup.subgroupOf`, `Subgroup.index`,
`Subgroup.Normal`, `QuotientGroup.mk`, quotient groups and coset spaces,
`IsClosed`, `Finite`, `CompactSpace`, `T2Space` and
`TotallyDisconnectedSpace` are Mathlib's.

## Targets and complete telescopes

Every target has the section binders implicit `{G : Type*}`, `[Group G]`
and `[TopologicalSpace G]`, with the single universe parameter `u_1`,
followed by the explicit and instance binders shown. The normality binder
`[hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]` is the
source binder `[hLnormal : (extensionSubgroup K.field L hLK).Normal]` with
the source abbreviation `extensionSubgroup` (M004.002) expanded to its exact
Mathlib body; likewise the finiteness binders `hLfinite`. Write `G_K` for
`K.field.toSubgroup`, `G_L` for `L.toSubgroup.subgroupOf K.field.toSubgroup`,
`I_L` for `D.extensionInertiaWithin K.field L hLK`, `Γ` for
`D.frobeniusClosure K L hLK σ`, `G_Σ ≤ G_K` for
`D.frobeniusFixedSubgroupWithin K L hLK σ` and `Σ` for the closed subgroup
`D.frobeniusFixedField K L hLK σ` of `G`.

```lean
def mem_frobeniusFixedSubgroupWithin_iffStatement (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) (k : K.field.toSubgroup) : Prop :=
    k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ ↔
      QuotientGroup.mk k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
```

An element `k ∈ G_K` lies in `G_Σ` exactly when its class in
`G_K ⧸ I_L` lies in `Γ`.

```lean
def frobeniusFixedSubgroupWithin_isClosedStatement (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    IsClosed
      (D.frobeniusFixedSubgroupWithin K L hLK σ : Set K.field.toSubgroup)
```

`G_Σ` is a closed subset of `G_K` with its subspace topology.

```lean
def mem_frobeniusFixedField_iffStatement (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) (g : G) : Prop :=
    g ∈ D.frobeniusFixedField K L hLK σ ↔
      ∃ k : K.field.toSubgroup,
        k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ ∧ k.1 = g
```

An element `g ∈ G` lies in `Σ` exactly when it is the image of some
`k ∈ G_Σ` under the inclusion `G_K → G`.

```lean
def frobeniusFixedField_leStatement (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    (D.frobeniusFixedField K L hLK σ).toSubgroup ≤ K.field.toSubgroup
```

`Σ` extends `K`: its subgroup is contained in `G_K`.

```lean
def extensionSubgroup_frobeniusFixedFieldStatement (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup =
      D.frobeniusFixedSubgroupWithin K L hLK σ
```

The subgroup of `G_K` cut out by `Σ` is exactly `G_Σ`. The source left side
is `extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ) (D.frobeniusFixedField_le K L hLK σ)`;
its abbreviation body is the displayed `subgroupOf`, and the inclusion proof
(the theorem M016.006) is not part of that body.

```lean
def extensionInertiaWithin_le_frobeniusFixedSubgroupWithinStatement
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    D.extensionInertiaWithin K.field L hLK ≤
      D.frobeniusFixedSubgroupWithin K L hLK σ
```

`I_L ≤ G_Σ` inside `G_K`.

```lean
def fieldInertia_le_frobeniusFixedFieldStatement (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    (D.fieldInertia L).toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ).toSubgroup
```

The ambient inertia group of `L` is contained in the subgroup of `Σ` in `G`.

```lean
def frobeniusFixedField_finiteStatement (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    Finite
      (K.field.toSubgroup ⧸
        (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup)
```

When `G` is a compact Hausdorff topological group and `G_L` has finite index
in `G_K`, the coset space of `G_K` modulo the subgroup of `G_K` cut out by
`Σ` is finite: `Σ | K` is finite. The source quotient is by
`extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ) (D.frobeniusFixedField_le K L hLK σ)`,
expanded as for M016.007. The hypothesis `hLfinite` is used only by the
source proof.

```lean
def frobeniusFixedField_index_le_extensionIndex_of_exponent_eq_oneStatement
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK)
    (hσ : D.frobeniusExponent K L hLK σ = 1) : Prop :=
    ((D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup).index ≤
      (L.toSubgroup.subgroupOf K.field.toSubgroup).index
```

When `G` is a compact, Hausdorff, totally disconnected topological group,
`G_L` has finite index in `G_K`, and the Frobenius exponent of `σ` is `1`,
the index of the subgroup of `G_K` cut out by `Σ` is at most the index of
`G_L`: `[Σ : K] ≤ [L : K]`. Both source sides use `extensionSubgroup`,
expanded as for M016.007. The hypotheses `hLfinite` and `hσ` are binders of
the proposition and are used only by the source proof.

```lean
def frobeniusFixedSubgroupWithin_inf_fieldInertiaWithinStatement
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    D.frobeniusFixedSubgroupWithin K L hLK σ ⊓
        D.fieldInertiaWithin K.field =
      D.extensionInertiaWithin K.field L hLK
```

When `G` is a compact, Hausdorff, totally disconnected topological group,
`G_Σ ⊓ I_K = I_L` as subgroups of `G_K`, where `I_K` is
`D.fieldInertiaWithin K.field`.

```lean
def frobeniusFixedField_fieldInertiaStatement (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    D.fieldInertia (D.frobeniusFixedField K L hLK σ) =
      D.fieldInertia L
```

Under the same hypotheses on `G`, the ambient inertia groups of `Σ` and of
`L` are equal closed subgroups of `G`: the maximal unramified extensions of
`Σ` and `L` coincide.

Binder order and kinds are those of the source theorems. No target has any
further hypothesis.

## Modification record

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the published names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The statements are copied
   verbatim, apart from the `extensionSubgroup` expansions in the binders
   and, for M016.007, M016.010 and M016.012, in the statements. Since the
   abbreviation `extensionSubgroup` ignores its inclusion-proof argument, the
   source argument `D.frobeniusFixedField_le K L hLK σ` (an application of the
   theorem M016.006) disappears from those statements, which therefore do
   not depend on M016.006. The source proofs are omitted: this contribution
   publishes proposition targets, and their proofs are separate work.
3. Omit the `@[simp]` attributes of M016.002 and M016.005, which cannot apply
   to proposition-valued definitions.
4. Precede the M016.010 and M016.012 targets by
   `set_option linter.unusedVariables false in`, because their named source
   binders `hLfinite` (and, for M016.012, `hσ`) do not occur in the
   propositions. The option only silences that linter warning and does not
   change the declarations.
5. Replace each source docstring by a description of the proposition
   beginning with `Target:`, and replace the source module docstring by a
   description of this module with a modification notice that names the
   source theorems.
6. Replace the source import by the published sibling module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Definitions`
   and the published module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Statements`
   (which provides the M014 names through its own import).
7. Omit `open CyclicCohomology`, which in these statements served only to
   resolve the expanded `extensionSubgroup`. Retain the noncomputable
   section and the variable line.
8. Omit all other source units, including the definition M016.011
   `frobeniusFixedFiniteExtension`. No helper declaration or instance is
   added.

These are the exact source statements as named propositions, without
published proofs. They discharge no host class-formation, cup, transfer,
Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Declaration inspection of
`frobeniusFixedField_index_le_extensionIndex_of_exponent_eq_oneStatement`
reported `statement_returns_prop: true`, the single universe parameter `u_1`
and the axioms `propext`, `Classical.choice` and `Quot.sound`. Compilation
and inspection are separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
