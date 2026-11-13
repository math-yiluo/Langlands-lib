# NYLL abstract reciprocity: same-base naturality restriction target

Worker 68, 13 November 2026.

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
| M075.008 | `finiteReciprocityNaturalityRestriction_sameBase_eq_restriction` | 509–519 | lines 520–524 |

The setting is a group `G` with a topology, closed subgroups `K`, `M`, `L` with
`hLM : L ≤ M` and `hMK : M ≤ K`, and the normality instances `hLnormal` of `L` and
`hMnormal` of `M`, both as subgroups of `K`.

`finiteReciprocityNaturalityRestriction_sameBase_eq_restrictionStatement K M L hLM hMK`
states that two homomorphisms `K ⧸ L → K ⧸ M` are equal:

- `finiteReciprocityNaturalityRestriction K K M L hMK (hLM.trans hMK) le_rfl hLM`, the
  Galois-side restriction map of norm–conjugation naturality (M066.001, Library module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.Restriction.Definitions`).
  It is used with both base fields equal to `K`, upper fields `M` (the target quotient)
  and `L` (the source quotient), the inclusion `K ≤ K` given by `le_rfl` and `hLM : L ≤ M`.
- `abstractReciprocityRestriction K M L hLM hMK`, the restriction in the upper exact row
  (M075.005, sibling module `Core/Restriction/Definitions`).

The hypotheses, including the instance arguments, are parameters of the `def` in the
source order and with the source binder kinds, and the value is exactly the source
conclusion. The instance arguments `hLnormal` and `hMnormal` are found by instance
resolution for both sides. The statement is not proved here.

## Name map

| Source | Adapted declaration |
| --- | --- |
| `ClassFormation.finiteReciprocityNaturalityRestriction_sameBase_eq_restriction` | `Langlands.NYLL.ClassFormation.finiteReciprocityNaturalityRestriction_sameBase_eq_restrictionStatement` |
| `ClassFormation.finiteReciprocityNaturalityRestriction` (used) | `Langlands.NYLL.ClassFormation.finiteReciprocityNaturalityRestriction` (Library) |
| `ClassFormation.abstractReciprocityRestriction` (used) | `Langlands.NYLL.ClassFormation.abstractReciprocityRestriction` (M075.005) |

## Modifications

- The source theorem becomes a Prop-valued `def` named after it with the suffix
  `Statement`, in the namespace `Langlands.NYLL.ClassFormation`. The complete source
  telescope, including the universe-polymorphic `{G : Type*}` binder and the named
  instance arguments, is retained in order; the proof is omitted. The docstring is
  rephrased as "Target of …".
- The source abbreviation M004.002 `CyclicCohomology.extensionSubgroup K L h`
  (`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 51–54, defined as
  `L.toSubgroup.subgroupOf K.toSubgroup`) is not in the Library; as the task context
  directs, it is replaced by its defining Mathlib term: `extensionSubgroup K L
  (hLM.trans hMK)` by `L.toSubgroup.subgroupOf K.toSubgroup` and `extensionSubgroup K M
  hMK` by `M.toSubgroup.subgroupOf K.toSubgroup`. The abbreviation ignores its proof
  argument, so the replacement is definitional.
- The instance names `hLnormal` and `hMnormal` do not occur in the conclusion; they are
  kept as parameters in their source positions, and `set_option
  linter.unusedVariables false in` silences the unused-variable linter.
- The unused section variables of `Core.lean` (`{G : IntegralRepGroupType}`,
  `{D : DegreeData G}`, `{A : Rep ℤ G}` and instances) are omitted; the declaration binds
  its own `{G : Type*}`. The source imports are replaced by imports of the Library module
  defining `finiteReciprocityNaturalityRestriction` and the sibling
  `Core/Restriction/Definitions` module.

## Validation

The module compiles in the project Lean service without errors or warnings, and the
declaration inspection reports `statement_returns_prop = true`. A private check
reconstructs the source declarations `finiteReciprocityNaturalityRestriction`,
`abstractReciprocityRestriction` and this statement verbatim (with a local
`extensionSubgroup` abbreviation matching the source definition) and proves, by `rfl`,
that the entire unapplied constants `finiteReciprocityNaturalityRestriction` and
`finiteReciprocityNaturalityRestriction_sameBase_eq_restrictionStatement` equal the
adapted ones. These checks establish compilation and source correspondence; independent
review is still required.
