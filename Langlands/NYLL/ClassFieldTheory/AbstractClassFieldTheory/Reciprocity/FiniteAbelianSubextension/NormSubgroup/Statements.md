# NYLL M296: order targets for finite abelian norm subgroups

Worker 449, 14 November 2026.

## Source

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
(file SHA-256 `f77cd402e62f7cd39a93a02269c2bfcffd9dc69b3919d352581a21d55aba67c0`),
scaffolding lines 30–34 and 404–411, theorem statements at lines 421–425 and
451–456. Registered source `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original
copyright and author header is retained; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

## Name map

Adapted names carry the prefix `Langlands.NYLL.ClassFormation.`, original names
the prefix `ClassFormation.`; `FAS` abbreviates `FiniteAbelianSubextension`.

| Unit | Original theorem | Source lines (statement; proof) | Adapted target |
| --- | --- | --- | --- |
| M296.031 | `FAS.normSubgroup_antitone` | 421–425; 425–449 | `FAS.normSubgroup_antitoneStatement` |
| M296.032 | `FAS.normSubgroup_compositum_le_inf` | 451–456; 456–459 | `FAS.normSubgroup_compositum_le_infStatement` |

The data they mention are published: `FAS` (M296.001) and its norm subgroup
`FAS.normSubgroup` (M296.030, sibling module
`FiniteAbelianSubextension/NormSubgroup/Definitions`), the field-inclusion
order on `FAS K` (M296.014, the instance
`Langlands.NYLL.PortInternal.M296.d014`) and the compositum
`FAS.compositum` (M296.017). The lattice operations on
`AddSubgroup (ambientFixedAddSubgroup A K)` are Mathlib's. No statement is proved
here.

## Statements

Both targets have implicit `{G : IntegralRepGroupType}`, `[Group G]`,
`[TopologicalSpace G]` and implicit `{K : ClosedSubgroup G}`, from the source
representation section variables (lines 407 and 411), and an explicit
coefficient module `(A : Rep ℤ G)` whose carrier universe is free.
`IntegralRepGroupType` is the published alias for `Type 0`. No
`IsTopologicalGroup G` or compactness assumption is added (only the excluded
M296.033 has them). Each target is a Prop-valued `def` whose body is the source
conclusion.

- **M296.031.** `normSubgroup_antitoneStatement (A : Rep ℤ G)
  {L₁ L₂ : FAS K} (h : L₁ ≤ L₂)` is `normSubgroup A L₂ ≤ normSubgroup A L₁`:
  if `L₁ ≤ L₂` in the field-inclusion order (that is, `G_{L₂} ≤ G_{L₁}`, so
  `L₁ ⊆ L₂` as fields), then the norm subgroup `N_{L₂/K} A_{L₂}` is contained in
  `N_{L₁/K} A_{L₁}` inside `A_K`. `L₁ L₂` are implicit and the hypothesis `h` is
  an explicit binder of the target, as in the source, so a proof of the target
  for all arguments is exactly the source theorem.
- **M296.032.** `normSubgroup_compositum_le_infStatement (A : Rep ℤ G)
  (L₁ L₂ : FAS K)` is
  `normSubgroup A (L₁.compositum L₂) ≤ normSubgroup A L₁ ⊓ normSubgroup A L₂`:
  the norm subgroup of the compositum `L₁L₂` lies in the intersection of the
  two norm subgroups, the unconditional half of `N_{L₁L₂} = N_{L₁} ∩ N_{L₂}`.
  `L₁ L₂` are explicit, as in the source.

## Modifications

1. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`; each
   theorem becomes a Prop-valued `def` named with the suffix `Statement`, and its
   proof is omitted. Binder names, binder kinds, the order of binders and the
   conclusions are unchanged.
2. M296.031 does not mention `h` in its conclusion;
   `set_option linter.unusedVariables false in` silences the linter for that
   declaration only.
3. The docstrings are prefixed "Target of …" and otherwise keep the source
   wording.
4. The source imports are replaced by the published modules for the norm
   subgroup (M296.030,
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.NormSubgroup.Definitions`),
   the order (M296.014,
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Order`)
   and the compositum (M296.017,
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Compositum`).
   `universe u` and the `GroupOnly` section (lines 36–402) are omitted, since the
   representation section does not use `u`; `open CyclicCohomology KummerTheory`
   is kept. The module docstring is replaced by a modification note, and the
   `noncomputable section` is left open to the end of the file, as in the
   source. Other source declarations are omitted; M296.033 is outside this
   module.

## Validation

The module compiles in the project Lean service (environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`) with no errors or warnings, and the
declaration inspection reports `statement_returns_prop = true` for both targets.
A private harness proves by `rfl` that each fully quantified target equals the
fully quantified source proposition, reconstructed verbatim from lines 423–425
and 453–456, and replays the source proof of M296.032 (lines 457–459) against
the targets, assuming M296.031 and the compositum order facts M296.018–.019.
These checks establish compilation and source correspondence only; independent
review is still required.
