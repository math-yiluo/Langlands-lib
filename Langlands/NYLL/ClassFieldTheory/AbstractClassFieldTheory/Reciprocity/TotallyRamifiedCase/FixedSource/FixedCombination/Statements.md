# NYLL abstract reciprocity: the fixed corrected combination

Worker 68, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean`,
inventory unit M084.001, `ClassFormation.abstractReciprocity_fixedCombination_of_commute`,
statement lines 31–37 (docstring 29–30; proof from line 38 on, omitted). Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original
copyright and author header is retained; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

`abstractReciprocity_fixedCombination_of_commuteStatement B g t hcomm c b a htc hgb hbc`
takes a group `Q` in universe zero (`{Q : IntegralRepGroupType}`, the published
`Langlands.NYLL.IntegralRepGroupType := Type 0`, M002.001), an integral representation
`B : Rep ℤ Q`, commuting elements `g t : Q` (`hcomm : Commute g t`) and vectors
`c b a : B.V` with

- `htc : B.ρ t c = c`,
- `hgb : B.ρ g b = B.ρ t b`,
- `hbc : b - c = B.ρ g a - a`,

and states `B.ρ g (b + a - B.ρ t a) = b + a - B.ρ t a`: the corrected combination
`b + a - t a` is fixed by `g`. The parameters are in the source order with the source
binder kinds. The statement is not proved here.

## Name map

| Source | Adapted declaration |
| --- | --- |
| `ClassFormation.abstractReciprocity_fixedCombination_of_commute` | `Langlands.NYLL.ClassFormation.abstractReciprocity_fixedCombination_of_commuteStatement` |
| `IntegralRepGroupType` (dependency, M002.001) | `Langlands.NYLL.IntegralRepGroupType` (published) |

## Modifications

- The source theorem becomes a Prop-valued `def` with the suffix `Statement` in the
  namespace `Langlands.NYLL.ClassFormation`. The proof is omitted and the docstring is
  rephrased as "Target of …".
- The conclusion does not mention `hcomm`, `c`, `htc`, `hgb` or `hbc`;
  `set_option linter.unusedVariables false in` silences the unused-variable linter for
  this declaration.
- The source section variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
  (line 27) are not used by this declaration and are omitted. The source imports and the
  unused openings `KummerTheory` and `CyclicCohomology` are replaced by the focused
  imports `Mathlib.RepresentationTheory.Rep.Basic` and the published
  `Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse`.

## Validation

The module compiles in the project Lean service without errors or warnings, and the
declaration inspection reports `statement_returns_prop = true`. A private check
reconstructs the source statement verbatim and proves equality of the entire unapplied
constants by `rfl` (reconstruction text adapted from Worker 196's private harness). These
checks establish compilation and source correspondence; independent review is still
required.
