# NYLL abstract reciprocity: restriction and finiteness targets

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
| M075.006 | `abstractReciprocityRestriction_mk` | 479–489 (`@[simp]` on 478) | line 490 (`rfl`) |
| M075.007 | `abstractReciprocityRestriction_surjective` | 493–501 | lines 502–505 |
| M075.009 | `abstractReciprocity_intermediateQuotient_finite` | 527–537 | lines 538–539 |
| M075.013 | `abstractReciprocity_lowerExtension_finite` | 620–627 | from line 628 on |

All four share the setting of the restriction map
`Langlands.NYLL.ClassFormation.abstractReciprocityRestriction` (M075.005, sibling module
`Core/Restriction/Definitions`): a group `G` with a topology, closed subgroups
`K`, `M`, `L` with `hLM : L ≤ M` and `hMK : M ≤ K`, and, where the source has them, the
normality instances `hLnormal`, `hMnormal` of `L` and `M` as subgroups of `K`.

- `abstractReciprocityRestriction_mkStatement K M L hLM hMK k` states that the restriction
  map sends the class of `k : K` in `K ⧸ L` to the class of `k` in `K ⧸ M`.
- `abstractReciprocityRestriction_surjectiveStatement K M L hLM hMK` states that the
  restriction map is surjective.
- `abstractReciprocity_intermediateQuotient_finiteStatement K M L hLM hMK` states, under
  the additional instance `hLfinite : Finite (K ⧸ L)`, that `K ⧸ M` is finite.
- `abstractReciprocity_lowerExtension_finiteStatement K M L hLM hMK` states, without
  normality hypotheses and under `hLfinite : Finite (K ⧸ L)`, that `M ⧸ L` is finite
  (here `L` is viewed as a subgroup of `M`).

In each case the hypotheses (including the instance arguments) are parameters of the
`def`, in the source order and with the source binder kinds, and the value is exactly
the source conclusion. The statements are not proved here.

## Name map

| Source | Adapted declaration |
| --- | --- |
| `ClassFormation.abstractReciprocityRestriction_mk` | `Langlands.NYLL.ClassFormation.abstractReciprocityRestriction_mkStatement` |
| `ClassFormation.abstractReciprocityRestriction_surjective` | `Langlands.NYLL.ClassFormation.abstractReciprocityRestriction_surjectiveStatement` |
| `ClassFormation.abstractReciprocity_intermediateQuotient_finite` | `Langlands.NYLL.ClassFormation.abstractReciprocity_intermediateQuotient_finiteStatement` |
| `ClassFormation.abstractReciprocity_lowerExtension_finite` | `Langlands.NYLL.ClassFormation.abstractReciprocity_lowerExtension_finiteStatement` |

## Modifications

- Each source theorem becomes a Prop-valued `def` named after it with the suffix
  `Statement`, in the namespace `Langlands.NYLL.ClassFormation`. The complete source
  telescope, including the universe-polymorphic `{G : Type*}` binder and the named
  instance arguments, is retained in order; the proofs are omitted. Docstrings are
  rephrased as "Target of …".
- The source abbreviation M004.002 `CyclicCohomology.extensionSubgroup K L h`
  (`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 51–54, defined as
  `L.toSubgroup.subgroupOf K.toSubgroup`) is not in the Library; as the task context
  directs, every occurrence is replaced by its defining Mathlib term:
  `extensionSubgroup K L (hLM.trans hMK)` by `L.toSubgroup.subgroupOf K.toSubgroup`,
  `extensionSubgroup K M hMK` by `M.toSubgroup.subgroupOf K.toSubgroup` and
  `extensionSubgroup M L hLM` by `L.toSubgroup.subgroupOf M.toSubgroup`. The
  abbreviation ignores its proof argument, so the replacement is definitional.
- Consequently some hypotheses (for example `hMK` in the last statement) and the
  instance arguments no longer occur in the conclusion. They are kept as parameters in
  their source positions; `set_option linter.unusedVariables false in` silences the
  unused-variable linter for each declaration.
- The source `@[simp]` attribute on `abstractReciprocityRestriction_mk` is dropped, since
  the new declaration is a proposition-valued definition, not a lemma.
- The unused section variables of `Core.lean` (`{G : IntegralRepGroupType}`,
  `{D : DegreeData G}`, `{A : Rep ℤ G}` and instances) are omitted; each declaration
  binds its own `{G : Type*}`. The source imports are replaced by an import of the
  sibling `Core/Restriction/Definitions` module.

Units M075.008 (`finiteReciprocityNaturalityRestriction_sameBase_eq_restriction`) and
M075.012 are not in this module: they depend on declarations that are not yet in the
Library.

## Validation

The module compiles in the project Lean service without errors or warnings, and for
each of the four declarations the declaration inspection reports
`statement_returns_prop = true`. A private check reconstructs each source declaration
verbatim (with a local `extensionSubgroup` abbreviation matching the source definition)
and proves equality of the entire unapplied constants with the adapted ones by `rfl`.
The reconstruction text was adapted from Worker 196's private harness. These checks
establish compilation and source correspondence; independent review is still required.
