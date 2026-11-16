# The defect of a linear form vanishes through degree one

This module proves
`Langlands.NYLL.PortInternal.M351.d029` with conclusion
`Langlands.NYLL.PortInternal.M351.d029Statement e ebar L q hq`.
For two Lubin–Tate series with the same prescribed linear coefficient, the
coefficient at `q` of the defect of `linearForm L` vanishes whenever the
total degree of `q` is at most one. The implicit and instance binders, in
order, are `{K : Type u} [Field K] {F : LocalField.{u, v} K}`
`{π : F.valuationSubring} {σ : Type w} [Fintype σ]`; the explicit
binders are `(e ebar : LubinTateSeries F π)`
`(L : σ → F.valuationSubring) (q : σ →₀ ℕ) (hq : q.degree ≤ 1)`.
There is no uniformizer hypothesis or additional premise.

## Source and attribution

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`,
SHA-256
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
Source lines 890–897 contain the private theorem
`LubinTate.SameUniformizer.coeff_defect_linearForm_eq_zero_of_degree_le_one`.
The source is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

Its registered source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Lean file retains the original copyright, Apache-2.0 and author header
and adds a dated modification record. The Library's
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. No patch10 edit
affects this source module.

## Implemented proof

Unfold the reducible target `d029Statement` and rewrite `linearForm L`
using `d027 L`. This turns the proposed intertwiner into
`∑ i, MvPowerSeries.monomial (Finsupp.single i 1) (L i)`.
Apply `d028 e ebar L Finset.univ q hq`. Its sum over `Finset.univ`
is definitionally the full sum just obtained, so `exact` closes the goal.
The `[Finite σ]` instance required by `d028` is inferred from the given
`[Fintype σ]`.

This follows the source proof: its rewrite uses
`linearForm_eq_sum_monomial_stabilization` (M351.027, source lines
829–839), and its final `simpa using` invokes
`coeff_defect_sum_linear_monomials_eq_zero` (M351.028, lines 842–888)
with `s = Finset.univ`. The adapted proof uses their published
`PortInternal.M351` names and exposes the proposition abbreviation before
rewriting.

## Imports and dependencies

The module has exactly three direct imports:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LowDegreeDefect.Statements`
  supplies the published `d029Statement` and, transitively, `linearForm`,
  `defect`, `LubinTateSeries`, `LocalField` and the Mathlib power-series
  and finite-sum definitions appearing in the target.
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LowDegreeDefect.LinearFormMonomialSum`
  supplies `Langlands.NYLL.PortInternal.M351.d027`.
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LowDegreeDefect.SumLinearMonomialsDefect`
  supplies `Langlands.NYLL.PortInternal.M351.d028`.

The proof body uses the two imported proof theorems, the reducible target
and `Finset.univ`. All imported statements and their dependencies are used
without changes. The external repository is solely a reading source.

## Adaptations

Worker 713 made the following changes to the selected source theorem:

- Extract the eight-line theorem from its original module into this
  focused Lean/Markdown pair.
- Rename the source-private theorem to the reserved public implementation
  name `Langlands.NYLL.PortInternal.M351.d029`, following the NYLL
  private-declaration port convention.
- Write out the original section binders in their source order and
  preserve universes `u`, `v`, `w`, implicit arguments and explicit
  arguments. Express the conclusion through the already-published
  `d029Statement`; its body is the original conclusion.
- Replace the original `RecursiveCoefficient` and Mathlib `Trunc` imports
  by the published focused target and prerequisite proof modules listed
  above.
- Unfold `d029Statement`, rewrite with the adapted name `d027 L` and
  replace the source's final `simpa using` by `exact d028 ...`.
- Omit the source module's unused `noncomputable section`,
  `open scoped BigOperators` and local `Classical.propDecidable`
  instance. This proof defines no data and needs no classical command.
- Replace the module exposition and theorem docstring with documentation
  of this selected result.

## Development verification

The complete focused module was compiled against published Library commit
`10e541e13546c013d0a33255669805da22b82ac3` in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with zero errors or warnings.
The theorem inspection retained the independent universe parameters `u`,
`v`, `w` and reported only `propext`, `Classical.choice` and `Quot.sound`.
Both prerequisite proof modules were already independently accepted and
published before this check. The task-supplied composition recipe from
Worker 495 is retained. Development compilation and inspection do not
establish independent semantic acceptance.
