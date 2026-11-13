# NYLL abstract reciprocity: inclusion in the upper exact row

Worker 68, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean`. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original
copyright and author header is retained; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

| Unit | Source declaration | Lines |
| --- | --- | --- |
| M075.010 | `ClassFormation.abstractReciprocityInclusion` | 543–556 (docstring 541–542) |

M075.010 is not in the task's unit table. Revision 3 of Task 5866 names it as the
same-module prerequisite of the listed M075.012 (`abstractReciprocity_galois_exact`),
whose statement mentions it, so it is ported here.

The setting is a group `G` with a topology, closed subgroups `K`, `M`, `L` with
`hLM : L ≤ M` and `hMK : M ≤ K`, and an instance `hLnormal` saying that `L` is normal as
a subgroup of `K`. `abstractReciprocityInclusion K M L hLM hMK` is the group
homomorphism `M ⧸ L → K ⧸ L` induced by the inclusion `M ≤ K`. In the field picture it is
`G(L/M) → G(L/K)`. The quotient `M ⧸ L` is a group only once `L` is normal in `M`. As in
the source, the type and the body therefore first make that normality available as a
local instance (`letI`). Its proof is the theorem M068.003
`transferNormNaturality_intermediateExtension_normal K M L hLM hMK`, which derives it
from `hLnormal`.

The body is, as in the source, the M071.001 definition
`Langlands.NYLL.ClassFormation.transferNormNaturalityIntermediateInclusion K M L hLM hMK`
(module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer.Intermediate.Definitions`).
That definition is in turn
`finiteReciprocityNaturalityRestriction K M L L (hLM.trans hMK) hLM hMK le_rfl`.

## Name map

| Source | Adapted declaration |
| --- | --- |
| `ClassFormation.abstractReciprocityInclusion` | `Langlands.NYLL.ClassFormation.abstractReciprocityInclusion` |
| `ClassFormation.transferNormNaturalityIntermediateInclusion` (used, M071.001) | `Langlands.NYLL.ClassFormation.transferNormNaturalityIntermediateInclusion` |
| `ClassFormation.transferNormNaturality_intermediateExtension_normal` (used, theorem M068.003) | `Langlands.NYLL.ClassFormation.transferNormNaturality_intermediateExtension_normal` (published proof, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransferFrobeniusGeometry.GroupOnly.U003.Proofs`) |

## Modifications

- The namespace gets the prefix `Langlands.NYLL`. Everything else is as in the source:
  the universe-polymorphic `{G : Type*}` binder, the explicit arguments, the named
  instance argument `hLnormal`, the type (including its `letI`) and the tactic body
  (`letI … := transferNormNaturality_intermediateExtension_normal K M L hLM hMK`, then
  `exact transferNormNaturalityIntermediateInclusion K M L hLM hMK`).
- The source abbreviation M004.002 `CyclicCohomology.extensionSubgroup K L h`
  (`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 51–54, defined as
  `L.toSubgroup.subgroupOf K.toSubgroup`) is not in the Library. As the task context
  directs, it is replaced by its defining Mathlib term:
  `extensionSubgroup K L (hLM.trans hMK)` becomes `L.toSubgroup.subgroupOf K.toSubgroup`,
  and `extensionSubgroup M L hLM` becomes `L.toSubgroup.subgroupOf M.toSubgroup`. The
  abbreviation ignores its proof argument, so the replacement is definitional.
- Both `letI` binders cite the published Library theorem
  `transferNormNaturality_intermediateExtension_normal`, the proof of M068.003, with the
  same arguments as the source. Its declared type is the published statement
  `transferNormNaturality_intermediateExtension_normalStatement K M L hLM hMK`, which by
  definition is `(L.toSubgroup.subgroupOf M.toSubgroup).Normal`, so the `letI`
  ascription is accepted by unfolding that definition. Its instance argument is the
  ambient `hLnormal`, as in the source. No proof is inlined and no hypothesis is added.
- The unused section variables of `Core.lean` (`{G : IntegralRepGroupType}`,
  `{D : DegreeData G}`, `{A : Rep ℤ G}` and their instances) are omitted. The source
  imports are replaced by imports of the M071.001 module and the M068.003 proof module.

No instance is introduced. The `letI` instances are local to the type and the body.

## Validation

The module compiles in the project Lean service with no errors or warnings. A private
check reconstructs verbatim the source declarations `finiteReciprocityNaturalityRestriction`,
`transferNormNaturalityIntermediateInclusion`, the theorem
`transferNormNaturality_intermediateExtension_normal` with its source proof, and
`abstractReciprocityInclusion`. It uses local copies of the source `extensionSubgroup` and
`mem_extensionSubgroup_iff`. It then proves by `rfl` that the whole unapplied constant
`abstractReciprocityInclusion` equals the adapted one, and likewise for
`transferNormNaturalityIntermediateInclusion`. It also checks that the Library theorem
proves the source proposition `(extensionSubgroup K' L hLK').Normal`. These checks
establish compilation and source correspondence; independent review is still required.
