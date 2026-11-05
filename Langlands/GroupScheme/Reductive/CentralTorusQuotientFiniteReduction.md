# The central torus quotient from three prerequisites

Author: Worker 1546. The proof is Worker 1428's proof of
`splitCentralTorusQuotient_of_prerequisites`
(`Reductive/CentralTorusQuotientReduction`), with one step replaced.

This module proves one theorem.

- `Langlands.GroupScheme.splitCentralTorusQuotient_of_prerequisites'`: the
  proposition `SplitCentralTorusQuotientStatement.{u}` follows from three
  prerequisite propositions, taken as explicit hypotheses:
  - `h1 : SplitTorusKernelCentralityStatement.{u}`;
  - `h3 : SplitTorusIsogenyOfLatticeMapsStatement.{u}`;
  - `h5 : CentralIsogenyMaximalTorusImageStatement.{u}`.

The theorem is conditional: it does not prove the three hypotheses. Compared
with `splitCentralTorusQuotient_of_prerequisites`, it drops the hypothesis
`h2 : CentralQuotientReductiveStatement.{u}` (reductivity of the quotient by an
arbitrary central subgroup). The quotient in this proof is the target of a
central isogeny, and for central isogenies reductivity of the target is
proved unconditionally by `isConnectedReductive_of_isCentralIsogeny`
(`Reductive/CentralFiniteQuotientReductive`).

## The proof

The proof is the proof of `splitCentralTorusQuotient_of_prerequisites`
(see the Markdown of `Reductive/CentralTorusQuotientReduction`), step for step,
with the following changes in its step 3 (the quotient).

- The published `exists_centralIsogeny_of_finite_central_subgroup` gives a
  smooth affine `Q`, a central isogeny `q : G ⟶ Q` (`hcq`) and the kernel
  equality. The proof does not form `RelativeRoot.IsFppfQuotient`.
- `Q` is connected reductive by
  `isConnectedReductive_of_isCentralIsogeny q hG hcq`, instead of by `h2`.

All other steps (the isogeny `t` by `h3`, centrality of the kernel of `t` in
`G` by `h1`, the descent of `i ≫ q` along `t` to `i'' : T' ⟶ Q`, closedness of
`i''`, and its maximality by `h5`) are unchanged. The conclusion is
`⟨Q, hQ, q, i'', hmax, hcq, hfac.symm⟩`.

The module imports `Reductive/CentralTorusQuotientReduction` for
`SubgroupFunctor.isNormal_of_le_center` and for its imports.

## Provenance

The proof route is internal, as for `splitCentralTorusQuotient_of_prerequisites`;
it follows the mathematical sketch in the Markdown of
`SplitCentralTorusQuotientStatement` (J. S. Milne, *Algebraic Groups*, 2017,
source `milne-2017-algebraic-groups`). Each step that is not a published
Library theorem or proved in `Reductive/CentralFiniteQuotientReductive` is one
of the three hypotheses, whose statement Markdown gives its own source
argument.

Checked with `lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
against Library commit `af00455e8e62bad8f10d229e6e3b908795bbf28f`
(diagnostic `6a9e6236-ce59-48ba-8c1e-7be9172bcad7`) and again against Library
commit `0bd5bf67c3464359bc8da3b3100163d6ee3da352` (diagnostic
`d36d4362-ae19-4303-b2e5-46bd5324db90`): 0 errors, 0 warnings,
axioms `propext`, `Classical.choice`, `Quot.sound`.
