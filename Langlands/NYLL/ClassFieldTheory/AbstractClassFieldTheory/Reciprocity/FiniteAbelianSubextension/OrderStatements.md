# NYLL M296.015 and M296.018–.020: order and compositum targets

Worker 448, 14 November 2026.

## Source

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
(file SHA-256 `f77cd402e62f7cd39a93a02269c2bfcffd9dc69b3919d352581a21d55aba67c0`),
scaffolding lines 30–52 and the theorem statements at lines 157–159 and
251–270. Registered source `external-lean-reuse-snapshots-2026-10-21`, content
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
| M296.015 | `FAS.le_iff` | 157–159; 160 | `FAS.le_iffStatement` |
| M296.018 | `FAS.le_compositum_left` | 251–253; 254–257 | `FAS.le_compositum_leftStatement` |
| M296.019 | `FAS.le_compositum_right` | 259–261; 262–265 | `FAS.le_compositum_rightStatement` |
| M296.020 | `FAS.compositum_le` | 267–270; 271 | `FAS.compositum_leStatement` |

The objects they mention are:

- `FAS`, `field` (M296.001–.002), from the published sibling module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions`;
- the order `≤` on `FAS K`, which is the M296.014 instance
  `Langlands.NYLL.PortInternal.M296.d014` of the sibling module
  `FiniteAbelianSubextension.Order` (submitted separately): `L₁ ≤ L₂` is defined
  as `L₂.field.toSubgroup ≤ L₁.field.toSubgroup`, field inclusion expressed by the
  opposite inclusion of absolute Galois subgroups;
- `FAS.compositum` (M296.017), of the sibling module
  `FiniteAbelianSubextension.Compositum` (submitted separately), whose closed
  subgroup is `L₁.field ⊓ L₂.field`.

No statement is proved here.

## Statements

Every target has implicit `{G : Type u}`, `[Group G]`, `[TopologicalSpace G]`
and implicit `{K : ClosedSubgroup G}`, from the source section variables
(lines 40 and 52), with no `IsTopologicalGroup G` assumption and the source
universe `u`. Each is a Prop-valued `def` whose body is the entire source
conclusion, and whose binders are the source binders.

- **M296.015.** `le_iffStatement (L₁ L₂ : FAS K)` is
  `L₁ ≤ L₂ ↔ L₂.field.toSubgroup ≤ L₁.field.toSubgroup`: the order on finite
  abelian subextensions is characterized by (reverse) containment of their
  closed subgroups, i.e. by containment of the fields.
- **M296.018.** `le_compositum_leftStatement (L₁ L₂ : FAS K)` is
  `L₁ ≤ L₁.compositum L₂`: `L₁` is contained in the compositum `L₁L₂`.
- **M296.019.** `le_compositum_rightStatement (L₁ L₂ : FAS K)` is
  `L₂ ≤ L₁.compositum L₂`: `L₂` is contained in the compositum `L₁L₂`.
- **M296.020.** `compositum_leStatement {L₁ L₂ P : FAS K} (h₁ : L₁ ≤ P)
  (h₂ : L₂ ≤ P)` is `L₁.compositum L₂ ≤ P`: the compositum is contained in every
  finite abelian subextension `P` containing both `L₁` and `L₂`, so it is their
  least upper bound. `L₁ L₂ P` are implicit and `h₁ h₂` explicit, as in the
  source; the hypotheses are binders of the target, so a proof of the target
  for all arguments is exactly the source theorem.

## Modifications

1. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`; each
   theorem becomes a Prop-valued `def` named with the suffix `Statement`, and
   its proof is omitted. Binder names, binder kinds, the order of binders and
   the conclusions are unchanged.
2. M296.020 does not mention `h₁` or `h₂` in its conclusion;
   `set_option linter.unusedVariables false in` silences the linter for that
   declaration only.
3. The docstrings are prefixed "Target of …" and otherwise keep the source
   wording.
4. The source imports are replaced by the sibling modules
   `FiniteAbelianSubextension.Order` (M296.014) and
   `FiniteAbelianSubextension.Compositum` (M296.017), which import the published
   data module. `open CyclicCohomology KummerTheory` is dropped: no name from
   either namespace occurs. The module docstring is replaced by a modification
   note. Source declarations other than these four theorem statements are
   omitted. As in the source, the `noncomputable section` is left open to the
   end of the file.

## Validation

The module compiles in the project Lean service (environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`) with no errors or warnings, and the
declaration inspection reports `statement_returns_prop = true`. A private
harness, also without errors or warnings, (a) reconstructs the four source
theorem statements verbatim with their source proofs (`Iff.rfl`; `change …;
exact inf_le_left`; `change …; exact inf_le_right`;
`fun _ hp => ⟨h₁ hp, h₂ hp⟩`) and uses them to prove theorems whose types are
the four targets applied to the same binders; and (b) proves by `rfl` that each
fully quantified target equals the fully quantified source proposition. These
checks establish compilation and source correspondence only; independent review
is still required.
