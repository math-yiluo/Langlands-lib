# NYLL M296: elementary finite abelian subextension targets

Worker 159, 13 November 2026.

## Source

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
(file SHA-256 `f77cd402e62f7cd39a93a02269c2bfcffd9dc69b3919d352581a21d55aba67c0`),
scaffolding lines 30–52 and theorem statements at lines 110–131. Registered
source `external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; attribution
supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original
copyright and author header is retained; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

## Name map

Adapted names carry the prefix `Langlands.NYLL.ClassFormation.`, original names
the prefix `ClassFormation.`; `FAS` abbreviates `FiniteAbelianSubextension`.

| Unit | Original theorem | Source lines (statement; proof) | Adapted target |
| --- | --- | --- | --- |
| M296.011 | `FAS.extensionQuotientMk_apply` | 110–116; 117 | `FAS.extensionQuotientMk_applyStatement` |
| M296.012 | `FAS.extensionQuotient_inductionOn` (protected) | 119–124; 125 | `FAS.extensionQuotient_inductionOnStatement` (protected) |
| M296.013 | `FAS.ext` | 127–131; 131–142 | `FAS.extStatement` |

The data they mention (`FAS`, `field`, `below`, `extensionQuotient` with its
`CommGroup` instance, `extensionQuotientMulEquiv`, `extensionQuotientMk`) are the
M296.001–.010 declarations of the sibling module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions`;
`extensionSubgroup` is the published
`Langlands.NYLL.CyclicCohomology.extensionSubgroup`. No statement is proved here.

## Statements

Every target has implicit `{G : Type u}`, `[Group G]`, `[TopologicalSpace G]`
and implicit `{K : ClosedSubgroup G}`, from the source section variables
(lines 40 and 52), with no `IsTopologicalGroup G` assumption and the source
universe `u`. Each is a Prop-valued `def` whose body is the source conclusion.

- **M296.011.** `extensionQuotientMk_applyStatement (L : FAS K)
  (k : K.toSubgroup)` is
  `L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
  (QuotientGroup.mk k : K.toSubgroup ⧸ extensionSubgroup K L.field L.below)`:
  the named abelian quotient projection, read through the comparison
  equivalence, is the ordinary quotient map.
- **M296.012.** `FAS.extensionQuotient_inductionOnStatement (L : FAS K)
  {motive : L.extensionQuotient → Prop} (q : L.extensionQuotient)
  (mk : ∀ k : K.toSubgroup, motive (L.extensionQuotientMk k))` is `motive q`:
  given the hypothesis `mk` that a predicate holds on every image of the
  canonical projection, it holds at an arbitrary quotient element `q`. The
  hypothesis `mk` is a binder of the target, as in the source theorem, so a
  proof of the target for all arguments is exactly the source elimination
  principle. The motive is implicit and the declaration is `protected`, as in
  the source.
- **M296.013.** `extStatement {L₁ L₂ : FAS K} (h : L₁.field = L₂.field)` is
  `L₁ = L₂`: two finite abelian subextensions with the same closed subgroup are
  equal. `L₁ L₂` are implicit and `h` explicit, as in the source.

## Modifications

1. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`; each
   theorem becomes a Prop-valued `def` named with the suffix `Statement`, and
   its proof is omitted. Binder names, binder kinds, the order of binders and
   the conclusions are unchanged; `protected` is kept on M296.012.
2. The attributes `@[simp]` (line 111) and `@[ext]` (line 129) are not attached
   to the Prop definitions; they belong to the later theorems that prove the
   targets.
3. M296.012 and M296.013 do not mention `mk` or `h` in their conclusions;
   `set_option linter.unusedVariables false in` silences the linter for those
   two declarations only.
4. The docstrings are prefixed "Target of …" and otherwise keep the source
   wording.
5. The import is the sibling published data module; `open KummerTheory` is
   dropped (no `KummerTheory` name occurs); the module docstring is replaced by a
   modification note; source declarations other than these three theorem
   statements are omitted (M296.001–.010 are in the `Definitions` module).
   As in the source, the `noncomputable section` is left open to the end of the
   file.

## Validation

The module compiles in the project Lean service (environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`) with no errors or warnings, and the
declaration inspection reports `statement_returns_prop = true`. A private
harness (a) reconstructs the three source theorem statements verbatim, with
the source proofs (for M296.011 and .012 the bodies of the corresponding
finite Galois lemmas, `rfl` and `Quotient.inductionOn'`), and uses them to prove
theorems whose types are the three targets applied to the same binders; and
(b) proves by `rfl` that each fully quantified target equals the fully
quantified source proposition. These checks establish compilation and source
correspondence only; independent review is still required.
