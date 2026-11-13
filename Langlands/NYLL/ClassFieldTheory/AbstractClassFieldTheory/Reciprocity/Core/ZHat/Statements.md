# NYLL abstract reciprocity: a profinite-integer step

Worker 68, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean`, inventory unit
M075.028, `abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero`, statement lines
1159–1163 (docstring 1157–1158; proof from line 1164 on, omitted). Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original
copyright and author header is retained; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

`abstractReciprocity_zHat_nsmul_eq_natCast_forces_zeroStatement n k hn hk z h` takes
natural numbers `n`, `k` with `hn : 0 < n` and `hk : k < n`, a profinite integer
`z : ZHat`, and `h : n • z = Int.castRingHom ZHat (k : ℤ)`, and states `k = 0`. That
is: if `n z = k` in `ℤ̂` with `0 ≤ k < n`, then `k = 0`. `ZHat` is the published
`Langlands.NYLL.ClassFormation.ZHat` (M008.008, module
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions`),
which the source declaration refers to as `ZHat` inside `namespace ClassFormation`. The
statement is not proved here.

## Name map

| Source | Adapted declaration |
| --- | --- |
| `ClassFormation.abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero` | `Langlands.NYLL.ClassFormation.abstractReciprocity_zHat_nsmul_eq_natCast_forces_zeroStatement` |
| `ClassFormation.ZHat` (dependency, M008.008) | `Langlands.NYLL.ClassFormation.ZHat` (published) |

## Modifications

- The source theorem becomes a Prop-valued `def` with the suffix `Statement` in the
  namespace `Langlands.NYLL.ClassFormation`; the binders `n k hn hk z h` are kept in the
  source order with the source binder kinds, the value is the source conclusion `k = 0`,
  and the proof is omitted. The docstring is rephrased as "Target of …".
- The hypotheses do not occur in the conclusion; `set_option linter.unusedVariables
  false in` silences the unused-variable linter for this declaration.
- The source section variables of `Core.lean` are unused by this declaration and are
  omitted. The source imports are replaced by the single import of the published
  `ProfiniteIntegerCore.Definitions` module, which supplies `ZHat` and its ring
  structure.

## Validation

The module compiles in the project Lean service without errors or warnings, and the
declaration inspection reports `statement_returns_prop = true`. A private check
reconstructs the source statement verbatim and proves equality of the entire
unapplied constants by `rfl` (reconstruction text adapted from Worker 196's private
harness). These checks establish compilation and source correspondence; independent
review is still required.
