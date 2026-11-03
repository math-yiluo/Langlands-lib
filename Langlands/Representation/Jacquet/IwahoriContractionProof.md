# Proof of the conditional Jacquet lemma and admissibility statements

`Langlands.Jacquet.iwahoriContractionJacquet.{uG,uV}` proves
`Langlands.Jacquet.IwahoriContractionJacquetStatement.{uG,uV}` from
`Langlands.Representation.Jacquet.IwahoriContractionStatements`. It adds no
hypotheses: every premise comes from the five quantified propositions.
The group universe `uG` and the carrier universe `uV` remain independent.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, VI.6.1 (printed pp.176–177, PDF pp.182–183).
The structural conditions it uses are V.5.2(ii)–(iv) (printed p.123, PDF p.129).
The registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The statement file records the conditional generalization and the scope of
each clause.

Worker 834 authored the reused aggregate proof and both helper implementations.
Worker 1004 checked the complete implementation against the current Library
and original source, preserved the Lean files unchanged, and revised the paired
English documentation for this focused proof.

## Route

The proof splits the conjunction. It discharges each clause with one theorem
from the two helper modules described below.

| Clause | Theorem used |
| --- | --- |
| `IwahoriContractionJacquetLemmaStatement` | `fixedJacquetMap_surjective_of_iwahoriContraction` |
| `IwahoriContractionKernelStatement` | `powerKernelSup_eq_ker_of_iwahoriContraction` |
| `IwahoriContractionStableImageStatement` | `stableImageJacquetMap_bijective_of_iwahoriContraction` |
| `IwahoriContractionAdmissibilityStatement` | `isAdmissible_action_of_iwahoriContraction` |
| `IwahoriContractionNormalizedAdmissibilityStatement` | `Aubert.General.isAdmissible_normalizedJacquetFunctor_obj_of_iwahoriContraction` |

The first four theorems are in
`Langlands.Representation.Jacquet.IwahoriContractionAdmissibility`. They work
for any topological group and any complex module, and their Markdown gives
their proofs. In outline:

- From the Iwahori factorization of `K`, the quotient class of the compressed
  vector `average_K(ρ(g)v)` equals the action of `g` on the class of `v`.
- Contraction and pointwise exhaustion of `N` show that a fixed vector with
  zero class is killed by a power of the compression operator. This gives the
  kernel clause, which needs no finite-dimensionality premise.
- If `V^K` is finite-dimensional, Fitting's decomposition gives
  `V^K = powerKernelSup ⊕ stableImage`. Together with the kernel clause, this
  makes the restricted quotient map injective. For surjectivity, lift a
  `K ∩ M`-fixed class `y` to `v`. Some `ρ(g^s)v` is fixed by `K ∩ Nbar`, so its
  `K`-average has class `π_N(g)^s y`. Compression is bijective on the stable
  image, which cancels the power of `g`. The weak Jacquet lemma is the
  surjectivity half.
- Admissibility follows from the basis hypothesis. For an open subgroup `L` of
  `M`, it supplies a compact open `K` with `K ∩ M ≤ L` and a witness `g`. The
  fixed vectors of `L` lie inside those of `K ∩ M`, which are finite-dimensional
  by the bijection.

The fifth theorem is in
`Langlands.Representation.Aubert.General.JacquetAdmissibility`. It unfolds the
normalized functor into a twist by the inverse half Haar-modulus character of
the localization at the trivial character. The twist has an open kernel, so it
preserves admissibility both ways. The trivial-character localization is
equivalent to the unnormalized action, so the fourth clause applies.

## Remaining obligations

The basis hypothesis `HasIwahoriContractionBasis` for the parabolic subgroups
of actual reductive rational-point groups remains a separate structural
obligation. The generalized kernel and stable image are formed from powers of
one compression operator. Comparing them with Renard's sufficiently contracting
single-operator kernel and image, and proving that the canonical section
depends only on `P` and `K`, remain separate obligations. Howe's theorem
VI.6.3, Jacquet finite generation VI.1.3 and the closed finite-length theorem
VI.6.4 are neither proved nor assumed here.
