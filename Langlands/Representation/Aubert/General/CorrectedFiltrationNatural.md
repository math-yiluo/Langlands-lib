# Naturality of the corrected support filtration

Author: Worker 757 (task `f7d95940-33d0-49d3-93d6-8d5ff8d89373`).

This module proves that the corrected support filtration of
`Aubert.General.CorrectedFiltration` (Worker 379) is natural in the ambient
smooth representation. Let `φ : A ⟶ B` be a morphism of smooth representations
of `G`. The actual functor map `r_I(i_J r_J φ) : r_I(E_J) ⟶ r_I(E'_J)` sends
each filtration step `Ẽ^{θ_i'}_{J,I}` of `A` into the same step of `B`. The
module packages the restricted maps as morphisms of the actual smooth
subrepresentations. Here `E_J = i_J r_J A`, `E'_J = i_J r_J B`, and `J = S \ s`
for the removed roots `s`, as in `CorrectedFiltration`.

## Declarations

The standard data `P M U h hclosed hδ hP hU`, the subgroup `T`, the finite
relative Weyl group and the Coxeter system `cs` are those of
`CorrectedFiltration`. The representations `A B C` lie in
`SmoothRep.{0, uG, max uG uV} ℂ G`.

* `termMap P M U h hclosed φ s : term … A s ⟶ term … B s` is the actual functor
  map `(inductionJacquetFunctor (h (S \ s)) (hclosed (S \ s))).map φ`, i.e.
  `i_J r_J φ`. `hom_termMap` says that its underlying intertwiner is Worker 194's
  `Complex.termMap` for the removed-root families (definitional).
  `termMap_id` and `termMap_comp` are the functor laws.
* `transition_termMap`: for `s ⊆ t`, the term maps commute with the actual
  transition maps,
  `transition A hst ≫ termMap φ t = termMap φ s ≫ transition B hst`.
  This is the published `Complex.termMap_natural`, transferred from the
  underlying linear maps to morphisms of smooth representations.
* `termMap_mem_inductionStep`: the term map sends `inductionStep … A I s i`
  (functions in `E_J` that vanish outside `G_{θ_i'}`) into
  `inductionStep … B I s i`. Normalized induction acts on equivariant functions
  by postcomposition with `r_J φ` (`normalizedInductionFunctor_map_eval`), and a
  linear map sends zero to zero. So a function that vanishes at `g` still
  vanishes at `g` after applying the term map.
* `termMap_mem_step`: the Jacquet image `r_I(termMap φ s)` sends
  `step … A I s i` into `step … B I s i`. This is the published
  `jacquetImage_map` applied to the previous item.
* `stepMap T cs φ I s i`: the restriction of `r_I(termMap φ s)` to these steps,
  as a morphism between the smooth subrepresentations
  `SmoothRep.subrepresentation (r_I(E_J)) (step … A I s i)` and the
  corresponding one for `B`. Its linear map is `LinearMap.restrict`, and it is
  intertwining because `r_I(termMap φ s)` is.
* `stepMap_apply`: the step map applies `r_I(termMap φ s)` to the underlying
  vector (definitional).
* `stepMap_subtype`: the square formed by the step map, the two actual
  inclusions `SmoothRep.subtype` and `r_I(termMap φ s)` commutes.

## Scope

The provenance is derived. Every statement follows directly from published
definitions: the support condition is pointwise, normalized induction acts
pointwise on functions, and Jacquet images of preserved submodules are
preserved. No literature assertion is added. The module exists so that
isomorphisms assembled from the filtration can be proved natural in the ambient
representation. It treats only the actual filtration of `CorrectedFiltration`.

The module needs no Bruhat cover, no orbit ordering, no graded identification
and no exhaustivity hypothesis. It proves nothing about the graded pieces,
their transition maps or their vanishing; those are the targets in
`CorrectedFiltrationStatements`. It also states no naturality lemma for graded
quotient maps. Such maps can be obtained from `stepMap` at `i` and `i + 1`
together with `step_monotone`.
