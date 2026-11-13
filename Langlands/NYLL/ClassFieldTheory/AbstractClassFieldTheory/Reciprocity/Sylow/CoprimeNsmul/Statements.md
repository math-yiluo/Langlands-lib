# NYLL abstract reciprocity: Sylow subgroups and coprime multiples

Worker 68, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Sylow.lean`, inventory unit
M078.005, `ClassFormation.FiniteGaloisSubextension.sylowAddSubgroup_le_nsmul_range_of_coprime`,
statement lines 144–150 (docstring 137–143; proof from line 151 on, omitted). Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original
copyright and author header is retained; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

`FiniteGaloisSubextension.sylowAddSubgroup_le_nsmul_range_of_coprimeStatement S hn` takes an
additive commutative group `B`, natural numbers `p` and `n` with `p` prime (instance
`[Fact p.Prime]`), a Sylow `p`-subgroup `S` of `Multiplicative B` and
`hn : Nat.Coprime n p`, and states that the additive subgroup of `B` corresponding to `S`
(`Subgroup.toAddSubgroup' S`) is contained in the range of the additive homomorphism
`nsmulAddMonoidHom n : B →+ B`, `x ↦ n • x`. That is: a Sylow `p`-subgroup of `B` lies in
`n B` when `n` is prime to `p`. The parameters `B`, `p`, `n` are implicit, `S` and `hn`
explicit, in the source order. The statement is not proved here.

## Name map

| Source | Adapted declaration |
| --- | --- |
| `ClassFormation.FiniteGaloisSubextension.sylowAddSubgroup_le_nsmul_range_of_coprime` | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.sylowAddSubgroup_le_nsmul_range_of_coprimeStatement` |

## Modifications

- The source theorem becomes a Prop-valued `def` with the suffix `Statement`, in the
  namespace `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension` (the source namespace
  `ClassFormation.FiniteGaloisSubextension`, lines 42–177, prefixed by `Langlands.NYLL`).
  The proof is omitted and the docstring is shortened to its first sentence, rephrased as
  "Target of …".
- The conclusion does not mention `hn`; `set_option linter.unusedVariables false in`
  silences the unused-variable linter for this declaration.
- The source section variables `{G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]` (line 40) and `{K : ClosedSubgroup G}` (line 44) are not used by
  this declaration and are omitted. The source imports are replaced by the focused import
  `Mathlib.GroupTheory.Sylow`.

## Validation

The module compiles in the project Lean service without errors or warnings, and the
declaration inspection reports `statement_returns_prop = true`. A private check
reconstructs the source statement verbatim inside a `FiniteGaloisSubextension` namespace
and proves equality of the entire unapplied constants by `rfl` (reconstruction text
adapted from Worker 196's private harness). These checks establish compilation and source
correspondence; independent review is still required.
