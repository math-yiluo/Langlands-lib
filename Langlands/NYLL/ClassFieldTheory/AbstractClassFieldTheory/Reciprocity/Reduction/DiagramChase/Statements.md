# NYLL abstract reciprocity: diagram-chase targets of the reductions

Worker 68, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean`. Registered
source `nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original
copyright and author header is retained; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

| Unit | Source theorem | Statement lines | Omitted proof |
| --- | --- | --- | --- |
| M077.032 | `abstractReciprocity_surjective_of_exact_diagram` | 670–683 | from line 684 |
| M077.033 | `abstractReciprocity_bijective_of_exact_diagram` | 707–722 | from line 723 |
| M077.034 | `abstractReciprocity_commutator_mem_kernel` | 751–755 | from line 756 |

The first two concern a diagram of additive groups (`AddGroup`, so the groups need not be
commutative) and additive homomorphisms

```
Q₀ --iQ--> Q --pQ--> Q₁
|r₀        |r        |r₁
v          v         v
B₀ --iB--> B --pB--> B₁
```

with commutativity hypotheses `hleft : ∀ q, r (iQ q) = iB (r₀ q)` and
`hright : ∀ q, pB (r q) = r₁ (pQ q)`.

- `abstractReciprocity_surjective_of_exact_diagramStatement … hexact hpQ hleft hright hr₀
  hr₁` states that `r` is surjective, given that the bottom row is exact at `B`
  (`hexact : Function.Exact iB pB`), `pQ` is surjective, and `r₀` and `r₁` are surjective.
- `abstractReciprocity_bijective_of_exact_diagramStatement … hexactQ hexactB hpQ hiB hleft
  hright hr₀ hr₁` states that `r` is bijective, given that both rows are exact at the
  middle (`Function.Exact iQ pQ`, `Function.Exact iB pB`), `pQ` is surjective, `iB` is
  injective, and `r₀` and `r₁` are bijective.
- `abstractReciprocity_commutator_mem_kernelStatement r q hq` takes a group `Q`, an
  additive commutative group `B`, an additive homomorphism `r : Additive Q →+ B` and an
  element `q` of the commutator subgroup `commutator Q`, and states
  `r (Additive.ofMul q) = 0`.

In each case the hypotheses are parameters of the `def`, in the source order and with the
source binder kinds (the six types `{Q₀ Q Q₁ B₀ B B₁ : Type*}` are implicit and
universe-polymorphic, as in the source), and the value is exactly the source conclusion.
The statements are not proved here.

## Name map

| Source | Adapted declaration |
| --- | --- |
| `ClassFormation.abstractReciprocity_surjective_of_exact_diagram` | `Langlands.NYLL.ClassFormation.abstractReciprocity_surjective_of_exact_diagramStatement` |
| `ClassFormation.abstractReciprocity_bijective_of_exact_diagram` | `Langlands.NYLL.ClassFormation.abstractReciprocity_bijective_of_exact_diagramStatement` |
| `ClassFormation.abstractReciprocity_commutator_mem_kernel` | `Langlands.NYLL.ClassFormation.abstractReciprocity_commutator_mem_kernelStatement` |

## Modifications

- Each source theorem becomes a Prop-valued `def` named after it with the suffix
  `Statement`, in the namespace `Langlands.NYLL.ClassFormation` (the source declarations
  lie directly in `ClassFormation`, after `end FiniteGaloisSubextension` on line 664). The
  proofs are omitted and the docstrings are rephrased as "Target of …".
- Since the conclusions do not mention the hypotheses,
  `set_option linter.unusedVariables false in` silences the unused-variable linter for
  each declaration.
- The source section `Representation` (lines 596–844) declares
  `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`; these variables are not
  used by the three declarations and are omitted, as is the unused `universe u`. The
  source imports are replaced by the focused Mathlib imports `Mathlib.Algebra.Exact.Basic`
  (for `Function.Exact`) and `Mathlib.GroupTheory.Commutator.Basic` (for `commutator`).

## Validation

The module compiles in the project Lean service without errors or warnings, and for each
of the three declarations the declaration inspection reports
`statement_returns_prop = true`. A private check reconstructs each source statement
verbatim and proves equality of the entire unapplied constants with the adapted ones by
`rfl` (reconstruction text adapted from Worker 196's private harness). These checks
establish compilation and source correspondence; independent review is still required.
