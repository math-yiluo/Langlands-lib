# NYLL M029.017–021: targets for the maximal unramified field

The paired Lean file gives five Prop-valued targets for the five source
theorems about the maximal unramified field. The source is Naganori
Yamaguchi's ClassFieldTheory (NYLL) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`
(file SHA-256
`7d4c7c59cd25c27a728b49b8b4df61649bc818d2ef7ff4fdc375a92ea13f7460`). The
registered source `external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`) has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Units

Adapted names use the prefix `Langlands.NYLL.ClassFormation.DegreeData.`.
Original names use the prefix `ClassFormation.DegreeData.`. The line ranges
include the docstrings.

| Unit | Original theorem | Source lines | Adapted target |
| --- | --- | --- | --- |
| M029.017 | `maximalUnramifiedField_eq_fieldInertia` | 210–216 (theorem at 213) | `maximalUnramifiedField_eq_fieldInertiaStatement` |
| M029.018 | `mem_maximalUnramifiedField_iff` | 218–225 (`@[simp]` at 220, theorem at 221) | `mem_maximalUnramifiedField_iffStatement` |
| M029.019 | `maximalUnramifiedField_le` | 227–231 (theorem at 228) | `maximalUnramifiedField_leStatement` |
| M029.020 | `maximalUnramifiedField_le_of_le` | 233–237 (theorem at 234) | `maximalUnramifiedField_le_of_leStatement` |
| M029.021 | `maximalUnramifiedField_mono` | 239–247 (theorem at 240) | `maximalUnramifiedField_monoStatement` |

All five lie in `section maximalUnramifiedFields` (source line 198) with the
variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 200), inside
`namespace DegreeData` (line 202). The file-level context is at lines 18–28:
`universe u`, `namespace ClassFormation`, the opens `KummerTheory` and
`CyclicCohomology` and `noncomputable section`.

## The targets

Every target takes implicit `{G : Type u}` and instance arguments
`[Group G] [TopologicalSpace G]`, then explicit `(D : DegreeData G)`.
`DegreeData` is the Library's `Langlands.NYLL.ClassFormation.DegreeData`
(M010.002), a continuous surjective degree homomorphism `d : G → Ẑ`
(`D.degree`, with values in the multiplicative copy `ZHatMul` of `Ẑ`). A field is represented contravariantly by a closed subgroup of
`G`, Mathlib's `ClosedSubgroup G`; a larger field has a smaller subgroup.
`D.maximalUnramifiedField L` is M029.016,
`Langlands.NYLL.ClassFormation.DegreeData.maximalUnramifiedField`, ported in
`Definitions.lean` of this directory: it is `D.fieldInertia L`, the
Library's `Langlands.NYLL.ClassFormation.DegreeData.fieldInertia`
(M010.012), the closed subgroup `L ⊓ D.inertia` with `D.inertia = ker d`.
So the maximal unramified extension `L̃` of `L` is represented by
`I_L = G_L ∩ ker d`.

Each body below is the source conclusion verbatim.

**M029.017** `maximalUnramifiedField_eq_fieldInertiaStatement` takes
explicit `(L : ClosedSubgroup G)`; its body is

```lean
D.maximalUnramifiedField L = D.fieldInertia L
```

an equality of closed subgroups: the maximal unramified field is the
absolute inertia subgroup of `L`.

**M029.018** `mem_maximalUnramifiedField_iffStatement` takes explicit
`(L : ClosedSubgroup G)` and `(g : G)`; its body is

```lean
g ∈ D.maximalUnramifiedField L ↔ g ∈ L ∧ D.degree g = 1
```

so `g` lies in `I_L` exactly when `g ∈ G_L` and `d(g) = 1`. The degree takes
values in the Library's `ZHatMul` (M010.001), the multiplicative copy of
`Ẑ`, whose `1` is `0 ∈ Ẑ`; so the condition says that `g` has degree zero.

**M029.019** `maximalUnramifiedField_leStatement` takes explicit
`(L : ClosedSubgroup G)`; its body is

```lean
(D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup
```

so `I_L ≤ G_L`: the field `L̃` contains `L`.

**M029.020** `maximalUnramifiedField_le_of_leStatement` takes implicit
`{L K : ClosedSubgroup G}` and explicit
`(_hLK : L.toSubgroup ≤ K.toSubgroup)` (source name `hLK`), i.e.
`G_L ≤ G_K`, so `L` contains `K`; its body is

```lean
(D.maximalUnramifiedField L).toSubgroup ≤ K.toSubgroup
```

so `I_L ≤ G_K`: the field `L̃` contains `K`.

**M029.021** `maximalUnramifiedField_monoStatement` takes implicit
`{K L : ClosedSubgroup G}` (in this source order) and explicit
`(_hLK : L.toSubgroup ≤ K.toSubgroup)` (source name `hLK`); its body is

```lean
(D.maximalUnramifiedField L).toSubgroup ≤
  (D.maximalUnramifiedField K).toSubgroup
```

so `I_L ≤ I_K`: if `L` contains `K`, then `L̃` contains `K̃`.

## Modifications

Worker 483 made these changes to the source:

- The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
- `Statement` is appended to each name. Each `theorem` becomes a `def`
  returning `Prop` whose body is the source conclusion.
- The `@[simp]` attribute of M029.018 is omitted: it belongs to the theorem,
  not to the Prop-valued target.
- In M029.020 and M029.021 the argument name `hLK` becomes `_hLK`, because
  the body does not refer to this proof (Lean's unused-variable linter
  otherwise warns). The parameter keeps its position, explicit binder kind
  and type, so a proof of the target takes it in the source order.
- The proofs (`rfl` for M029.017, rewriting with M029.017 for M029.018–019,
  `(D.maximalUnramifiedField_le L).trans hLK` for M029.020 and an
  element-wise argument through M029.018 for M029.021) are not ported.
  Proving the targets is separate `lean.proof@1` work.
- The docstrings are adapted to say that each definition is a target. For
  M029.019 and M029.020 they also describe what the conclusion states: the
  source docstrings ("Every finite unramified field lies below the maximal
  unramified field" and "A field containing all finite unramified fields
  contains the maximal unramified field") speak of finite unramified fields,
  which the conclusions do not mention; the conclusions only compare `I_L`
  with `G_L` and `G_K`. The targets keep the source conclusions, and the
  adapted docstrings state those comparisons. The M029.017 docstring drops the
  source's advice about unfolding, which concerns the theorem.
- The module holds only these five targets. The data declarations of
  `NormSubgroup.lean` are in `Definitions.lean` of this directory, which this
  module imports; the `infiniteNorms` section and the theorems after line 247
  are omitted.
- `open KummerTheory` and `open CyclicCohomology` are omitted: the targets
  use neither namespace, and the Library has no `KummerTheory` namespace.
  `universe u`, `noncomputable section`, the section, the variable line and
  `namespace DegreeData` are kept.
- The source imports `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements`
  and `Nyll.GaloisCohomology.Cyclic.IntegralRepUniverse` are replaced by the
  single focused import
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions`,
  which provides `maximalUnramifiedField` and, through its own imports,
  `DegreeData` and `fieldInertia`.

The universe `u`, binders, binder kinds and their order, and the bodies are
otherwise unchanged. A focused `lean_check` of this module reports no errors
or warnings; each target returns `Prop` and has the single universe
parameter `u`.

## Scope

This unit states M029.017–021 and proves none of them. No norm-subgroup,
reciprocity, class-formation or cohomological theorem is asserted here.

## Licence

The original copyright, Apache-2.0 release and author header are kept at the
top of the Lean file, followed by a modification notice. The retained files
are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
