# NYLL abstract reciprocity: comparison of finite norm subgroups in a tower

Worker 68, 14 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean`. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original
copyright and author header is retained; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

| Unit | Source theorem | Statement lines | Omitted proof |
| --- | --- | --- | --- |
| M075.014 | `ClassFormation.abstractReciprocity_finiteNormSubgroup_le` | 656–667, up to `:= by` (docstring 654–655) | lines 668–678 |

The setting is a group `G : IntegralRepGroupType` (that is, `Type 0`, as `Rep ℤ G`
requires) with a group structure and a topology, an integral representation
`A : Rep ℤ G`, and closed subgroups `K`, `M`, `L` with `hLM : L ≤ M` and `hMK : M ≤ K`.
In the field picture `K ⊆ M ⊆ L` is a tower of fields, with `K`, `M`, `L` the
corresponding Galois groups. Three instance arguments say that the three relevant coset
spaces are finite:

- `hKMfinite`: `K ⧸ M` is finite, so `M | K` is a finite extension;
- `hMLfinite`: `M ⧸ L` is finite, so `L | M` is a finite extension;
- `hKLfinite`: `K ⧸ L` is finite, so `L | K` is a finite extension.

Here `K ⧸ M` means the coset space of `M.toSubgroup.subgroupOf K.toSubgroup` in
`K.toSubgroup`, and similarly for the others.

`abstractReciprocity_finiteNormSubgroup_leStatement A K M L hLM hMK` says

`finiteNormSubgroup A K L (hLM.trans hMK) ≤ finiteNormSubgroup A K M hMK`,

an inequality of additive subgroups of `ambientFixedAddSubgroup A K` (the fixed module
`A_K`). The published M039.001 definition `finiteNormSubgroup A K L h` is the range of the
relative norm `relativeNorm A K L h : A_L →+ A_K` (M024.009). So the statement is
`N_{L/K} A_L ⊆ N_{M/K} A_M`: every norm from `L` to `K` is a norm from `M` to `K`. The
source proof writes `N_{L/K} a` as `N_{M/K} (N_{L/M} a)` by norm transitivity. The
instance `hMLfinite` is used only by that omitted proof, but it stays a parameter as in
the source.

The hypotheses, including the instance arguments, are parameters of the `def`, in the
source order and with the source binder kinds and names. The value is exactly the source
conclusion. The statement is not proved here.

## Name map

| Source | Adapted declaration |
| --- | --- |
| `ClassFormation.abstractReciprocity_finiteNormSubgroup_le` | `Langlands.NYLL.ClassFormation.abstractReciprocity_finiteNormSubgroup_leStatement` |
| `ClassFormation.finiteNormSubgroup` (used, M039.001) | `Langlands.NYLL.ClassFormation.finiteNormSubgroup` (published, module `Reciprocity/Construction/FiniteNormQuotient/Definitions`) |
| `ClassFormation.relativeNorm` (used through M039.001, M024.009) | `Langlands.NYLL.ClassFormation.relativeNorm` (published) |
| `KummerTheory.ambientFixedAddSubgroup` (type of the subgroups) | `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` (published) |

## Modifications

- The source theorem becomes a Prop-valued `def` with the same name plus the suffix
  `Statement`, in the namespace `Langlands.NYLL.ClassFormation`. The complete source
  telescope is kept in order, including the named instance arguments `hKMfinite`,
  `hMLfinite` and `hKLfinite`. The proof is omitted. The docstring is rephrased as
  "Target of …".
- The source section variable `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
  is kept as a section variable, with the source comment. The unused section variables
  `{D : DegreeData G} {A : Rep ℤ G}` of `Core.lean` are omitted; the explicit binder
  `(A : Rep ℤ G)` of the theorem shadows the second in the source anyway.
- The source abbreviation M004.002 `CyclicCohomology.extensionSubgroup K L h`
  (`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 51–54, defined as
  `L.toSubgroup.subgroupOf K.toSubgroup`) is not in the Library. As the task context
  directs, it is replaced by its defining Mathlib term:
  - `extensionSubgroup K M hMK` becomes `M.toSubgroup.subgroupOf K.toSubgroup`;
  - `extensionSubgroup M L hLM` becomes `L.toSubgroup.subgroupOf M.toSubgroup`;
  - `extensionSubgroup K L (hLM.trans hMK)` becomes `L.toSubgroup.subgroupOf K.toSubgroup`.

  The abbreviation ignores its proof argument, so the replacement is definitional. The
  published `finiteNormSubgroup` already states its finiteness instance with
  `subgroupOf`.
- Because `hMLfinite` is not used in the statement, the unused-variables linter is
  disabled for this one declaration (`set_option linter.unusedVariables false in`), so
  the source name is kept. The published M039 statement module does the same for the
  source name `h`.
- The source imports are replaced by one import of the published module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions`,
  which provides `finiteNormSubgroup` and, through its imports, `relativeNorm`,
  `ambientFixedAddSubgroup` and `IntegralRepGroupType`. The source `open` commands are not
  needed and are omitted.

## Validation

The module compiles in the project Lean service with no errors or warnings, and the
declaration inspection reports `statement_returns_prop = true`. A private check restates
the source abbreviation `extensionSubgroup`, the source definition `finiteNormSubgroup`
(over the published `relativeNorm`) and the source statement verbatim. It then proves by
`rfl` that the source `finiteNormSubgroup` equals the published one, and that the whole
unapplied source constant equals `abstractReciprocity_finiteNormSubgroup_leStatement`.
These checks establish compilation and source correspondence; independent review is
still required.
