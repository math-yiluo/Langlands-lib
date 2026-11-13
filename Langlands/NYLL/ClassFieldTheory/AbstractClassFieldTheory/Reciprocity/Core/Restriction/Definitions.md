# NYLL abstract reciprocity: restriction in the upper exact row

Worker 68, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean`, inventory unit
M075.005, lines 457–472 (with its docstring on line 456). Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original
copyright and author header is retained; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

Let `G` be a group with a topology and let `K`, `M`, `L` be closed subgroups with
`L ≤ M ≤ K` (hypotheses `hLM` and `hMK`). Assume that `L` and `M`, viewed as subgroups
of `K`, are normal in `K` (instance arguments `hLnormal` and `hMnormal`). In the Galois
dictionary of the source these are the Galois groups of a tower of Galois extensions
`K ⊆ M ⊆ L`, and `K ⧸ L` is `G(L/K)`. The definition
`abstractReciprocityRestriction K M L hLM hMK` is the group homomorphism

`K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup →*
K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup`

induced by the identity of `K` through `QuotientGroup.map`, which is well defined
because `L ≤ M`. It is the restriction `G(L/K) → G(M/K)` in the upper row of the
reciprocity reduction diagram.

## Name map

| Source | Adapted declaration |
| --- | --- |
| `ClassFormation.abstractReciprocityRestriction` | `Langlands.NYLL.ClassFormation.abstractReciprocityRestriction` |

## Modifications

- The declaration is placed in the namespace `Langlands.NYLL.ClassFormation` instead of
  `ClassFormation`. The name, docstring, universe-polymorphic `{G : Type*}` binder,
  parameter and instance telescope (names, binder kinds and order) and the tactic body
  (`apply QuotientGroup.map … (MonoidHom.id K.toSubgroup)`, `intro k hk`,
  `exact hLM hk`) are unchanged.
- The source abbreviation M004.002 `CyclicCohomology.extensionSubgroup K L h`, defined
  in `Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean` (lines 51–54) as
  `L.toSubgroup.subgroupOf K.toSubgroup`, is not in the Library. As the task context
  directs, every occurrence is replaced by that defining Mathlib term:
  `extensionSubgroup K L (hLM.trans hMK)` becomes `L.toSubgroup.subgroupOf K.toSubgroup`
  and `extensionSubgroup K M hMK` becomes `M.toSubgroup.subgroupOf K.toSubgroup`. The
  abbreviation ignores its containment-proof argument, so this replacement is
  definitional.
- After this replacement `hMK` no longer occurs in the type or body. It is kept as an
  explicit parameter in its source position so that the call pattern
  `abstractReciprocityRestriction K M L hLM hMK` is unchanged.
  `set_option linter.unusedVariables false in` silences the resulting linter warning
  only for this declaration.
- The source section variables of `Core.lean` (`{G : IntegralRepGroupType}`,
  `{D : DegreeData G}`, `{A : Rep ℤ G}` and their instances) are not used by this
  declaration, which binds its own `{G : Type*}`, so they are omitted. The source's
  broad imports and namespace openings are replaced by the focused Mathlib imports
  `Mathlib.Topology.Algebra.Group.ClosedSubgroup` and
  `Mathlib.GroupTheory.QuotientGroup.Defs`.

No instance is introduced. This file contains only this one definition; the related
statement targets are in the sibling module `Core/Restriction/Statements`.

## Validation

The module compiles in the project Lean service without errors or warnings. A private
check reconstructs the source declaration verbatim (with a local `extensionSubgroup`
abbreviation matching the source definition) and proves
`@Langlands.NYLL.ClassFormation.abstractReciprocityRestriction = @reconstruction` by
`rfl`. The reconstruction text was adapted from Worker 196's private harness. These
checks establish compilation and source correspondence; independent review is still
required.
