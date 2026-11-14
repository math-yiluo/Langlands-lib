# NYLL M296.014: the field-inclusion order on finite abelian subextensions

Worker 448, 14 November 2026.

## Source

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
(file SHA-256 `f77cd402e62f7cd39a93a02269c2bfcffd9dc69b3919d352581a21d55aba67c0`),
scaffolding lines 30–52, the anonymous instance at lines 144–155 (docstring
144–145, command 146–155; the task cites it as lines 146–154), and the proof of
`FiniteAbelianSubextension.ext` at lines 132–142, which is copied into the
antisymmetry proof (modification 3). Registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; attribution
supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original
copyright and author header is retained; see `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).

## Name map

`FAS` abbreviates `FiniteAbelianSubextension`.

| Unit | Original | Source lines | Adapted name | Kind |
| --- | --- | --- | --- | --- |
| M296.014 | anonymous instance in namespace `ClassFormation.FAS` | 144–155 | `Langlands.NYLL.PortInternal.M296.d014` | global instance `PartialOrder (FAS K)` |

The source instance has no name. The task reserves the name
`Langlands.NYLL.PortInternal.M296.d014`; the instance is declared inside the
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension` namespace as
`_root_.Langlands.NYLL.PortInternal.M296.d014`, so its full name is exactly the
reserved one.

## Telescope and object

The source scaffolding is kept: `noncomputable section` (line 30),
`namespace ClassFormation` (32, prefixed), `universe u` (36),
`section GroupOnly` (38) with
`variable {G : Type u} [Group G] [TopologicalSpace G]` (40), and
`namespace FiniteAbelianSubextension` (50) with
`variable {K : ClosedSubgroup G}` (52). The instance therefore has implicit
`{G : Type u}`, `[Group G]`, `[TopologicalSpace G]` and implicit
`{K : ClosedSubgroup G}`. No `IsTopologicalGroup G` assumption is imposed, and
the source universe `u` is kept.

**M296.014.** `PartialOrder (FiniteAbelianSubextension K)` with

- `le L₁ L₂ := L₂.field.toSubgroup ≤ L₁.field.toSubgroup`. A finite abelian
  subextension `L` is represented by its closed subgroup `L.field = G_L` of
  `G`, so `L₁ ≤ L₂` means that `L₁` is contained in `L₂` as a field, which is
  the reverse (opposite) inclusion `G_{L₂} ≤ G_{L₁}` of subgroups. This
  opposite-subgroup order is preserved exactly; it unfolds by `rfl`.
- `le_refl _ := le_rfl` and `le_trans _ _ _ h₁₂ h₂₃ := h₂₃.trans h₁₂`, as in
  the source.
- `le_antisymm`: from `G_{L₂} ≤ G_{L₁}` and `G_{L₁} ≤ G_{L₂}` the two
  subgroups are equal, hence the closed subgroups are equal
  (`ClosedSubgroup.ext`), hence the two packages are equal by extensionality.
- `lt` and `lt_iff_le_not_ge` take Mathlib's default values, as in the source
  (which also leaves them out).

The instance is global, as the anonymous source instance is; it is the only
`PartialOrder` instance on `FiniteAbelianSubextension K` in the Library at the
base commit, and the only declaration this module adds.

## Reused Library declarations

- `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension` (M296.001) and its
  abbreviation `field` (M296.002), from the published module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions`,
  together with the published finite Galois structure underneath it.
- Mathlib's `PartialOrder`, `ClosedSubgroup`, `ClosedSubgroup.ext`,
  `Subgroup`, `le_rfl`, `le_antisymm` and `LE.le.trans`.

## Modifications

Worker 448 made only these changes:

1. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
2. The anonymous instance is named `_root_.Langlands.NYLL.PortInternal.M296.d014`
   (modification required by the task, see the name map). It stays a global
   instance with default priority.
3. The source proof of `le_antisymm` begins with `apply ext`, where `ext` is
   the source theorem `FiniteAbelianSubextension.ext` (M296.013). The Library
   states that theorem only as the target
   `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.extStatement` and
   does not yet prove it, so the antisymmetry proof first introduces a local
   `have ext : ∀ {L₁ L₂ : FiniteAbelianSubextension K}, L₁.field = L₂.field →
   L₁ = L₂`, the source statement of `ext` (lines 130–131) with its binders
   moved into the type, proved by the source proof (lines 132–142) unchanged
   after `intro L₁ L₂ h`. The rest of the proof (lines 151–155: `apply ext`,
   `apply ClosedSubgroup.ext`, the `have hs` and the final `exact`) is
   unchanged. Two comment lines mark the local copy. This affects only a
   proof field; the order relation itself is the source one.
4. The source imports
   `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension`,
   `Mathlib.Algebra.Group.Subgroup.Pointwise` and
   `Mathlib.Topology.Algebra.Group.Pointwise` are replaced by the single published
   module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions`.
5. `open CyclicCohomology KummerTheory` (line 34) is dropped: the instance uses
   no name from either namespace.
6. The source module docstring (lines 11–26) is replaced by a short docstring
   recording these modifications.
7. Only the instance (lines 144–155) is ported. The data M296.001–.010 are in
   the sibling `Definitions` module, the targets M296.011–.013 in `Statements`,
   the compositum M296.017 in `Compositum` and the targets M296.015 and
   M296.018–.020 in `OrderStatements`; base change, intersection and the other
   source declarations belong to other tasks. As in the source, the
   `noncomputable section` is left open to the end of the file.

The docstring, binders and the order relation are otherwise unchanged.

## Validation

The module compiles in the project Lean service (environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings. A
private harness checked, also without errors or warnings, that
`(L₁ ≤ L₂) = (L₂.field.toSubgroup ≤ L₁.field.toSubgroup)` holds by `rfl`, that
instance search finds this instance (`inferInstance` equals
`Langlands.NYLL.PortInternal.M296.d014` by `rfl`), that the source proof of
`le_iff` (`Iff.rfl`) proves the sibling target `le_iffStatement`, and that
the copied `ext` proof proves the published target `extStatement`. These checks
establish compilation and source correspondence only; independent review is
still required.
