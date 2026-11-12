# Symmetric tuple charts of a separated algebraic space

Author: Worker 75. The construction of the charts `e_n` (`exists_chart`) is copied from Worker 80's
draft proof of `UniformFieldPointChartsStatement` (Task 5417). A helper module of the proof of
`Langlands.AlgebraicGeometry.LangWeil.SpaceUniformLangWeilOfFamilyStatement`. Provenance:
internal. The construction follows Stacks Project, Lemma 68.8.3 (Tag 0BBN), through the
Library's tuple machinery for étale equivalence relations.

## Contents

- `SepChart` bundles a separated algebraic space `X` over `S0 = Spec (ULift ℤ)`, an affine
  étale surjective chart `a : U → X`, and a kernel pair `R ⇉ U` of `a` with étale projections
  `t, s`. `SepChart.exists_of_chart` makes one from any affine étale surjective chart
  (`exists_kernelPair`).
- Since `X` is separated, `R` is affine (`isAffine_of_isPullback_of_closedDiagonal`), and the
  joint map `(t, s) : R → U × U` is a closed immersion (`isClosedImmersion_lift`, transported
  from the closed-immersion statement over `S0` through the product comparison of
  `Over.forget`, an equivalence because `S0` is terminal).
- `E` is the étale equivalence relation `R ⇉ U` (`EtaleEquivalenceRelation.ofKernelPair`), so
  the Library's tuple constructions apply to it: the scheme of distinct related
  `(n + 1)`-tuples `W_n` (`tupleDistinctScheme`), the free action of the symmetric group, the
  affine quotient `V_n = W_n / S_{n+1}` (`tupleSymmetricScheme`) with quotient map `symMap`, and
  the bound `N = tupleLengthBound` on the lengths of distinct related tuples.
- `tupleOver`, `projOver`, `quot`, `quotMap` place `W_n`, its coordinates, `V_n` and the
  quotient map over `S0`; `map_projOver` says all coordinates of a related tuple have the same
  image in `X` (they differ by a section of `R`).
- `exists_chart`, `e`, `e_isEtale`, `quotMap_e`: the first coordinate `W_n → U → X` is invariant
  under the symmetric group, so it descends along the finite étale quotient map to
  `e_n : V_n → X` (`FiniteActionChart.exists_desc`, using that `X` is a sheaf). It is étale,
  because its composite with the finite étale surjection `W_n → V_n` is étale
  (`isEtale_of_finiteEtale_comp`).
