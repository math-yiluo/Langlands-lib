# Assembly of the target-local finiteness criterion

Module `Langlands.Geometry.Analytic.FullRecognitionFiniteTargetLocalityOfDescent`.

## Purpose

This module proves
`Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteOverTargetLocalityStatement`
conditionally on one named premise, effective finite Banach affinoid algebra
descent (`FiniteAffinoidAlgebraDescentStatement`). It is an intermediate result:
it is not an unconditional proof of the target statement. Once the descent
statement is proved in the Library, the unconditional theorem is the
application of `finiteOverTargetLocality_of_descent` to that proof.

The argument combines three ingredients proved in companion modules:

1. the finite subordinate refinement and its local finite models
   (`FullRecognitionFiniteTargetRefinement`, `g.HasFiniteTargetFamilies`,
   `hfam.refinement`, `F.models`);
2. Hausdorffness of the literal preimage `V ∩ g⁻¹(W.locus)`
   (`FullRecognitionFiniteTargetHausdorff`,
   `StrongHom.t2Space_inter_preimage_locus_of_targetFamilies`);
3. recognition of an effective descended parent as a recognized source affinoid
   with a finite Banach pullback (`FullRecognitionFiniteTargetRecognition`,
   `F.preimage`, `F.preimage_locus`, `F.preimage_admissible`,
   `F.pullback_isFiniteBanach`).

The only external input not proved here or in those modules is effective finite
Banach affinoid algebra descent,
`Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescentStatement`,
taken as an explicit hypothesis `hdesc`. It is not assumed as an axiom.

## Provenance

The route is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), Lemma 1.3.7, (a) implies (b) (printed pp. 27–28, PDF pp. 24–25;
registered source `berkovich-1993-etale-cohomology`). Given an arbitrary
affinoid domain `W` of the target inside `U`, the source refines `W` into
finitely many affinoid domains subordinate to the neighborhood families, over
each of which the preimage is affinoid with a finite algebra map, and then
applies Kiehl's theorem to glue the finite algebras. The descent of finite
algebras is Kiehl's theorem (Berkovich 1993, Theorem and Remark 1.2.1(ii),
printed p. 15), here the hypothesis `hdesc`. The assembly below is the
bookkeeping of that argument in the project's formalization.

## Declarations

Namespace `Langlands.Analytic.AffinoidAtlasPresentation.StrongHom`. Throughout,
`K` is any complete ultrametric normed field (trivial valuations allowed),
`A B : AffinoidAtlasPresentation.{u, v, w} K` with independent universes, and
`g : StrongHom A.saturatedPresentation B.saturatedPresentation`.

- `isFiniteOver_of_effectiveRefinements g V U hVU hfam hreal`: for
  `V ⊆ A.space`, `U ⊆ B.space` with `g.baseMap '' V ⊆ U`, under the target
  family hypothesis `hfam : g.HasFiniteTargetFamilies V U`, if every family
  refinement `F` of every recognized target affinoid `W` has an effective
  realization of its finite algebra descent data
  `F.models.algebraDescentData` (`hreal`), then `g.IsFiniteOver V U`.
  No openness of `V` or `U` and no global Hausdorffness is used.
- `finiteOverTargetLocality_of_descent hdesc :
  FiniteOverTargetLocalityStatement.{u, v, w} K`: the criterion, given
  `hdesc : FiniteAffinoidAlgebraDescentStatement.{u}`. It is declared with
  `def` rather than `theorem` because its type is a proposition and it is
  recorded as a supporting definition artifact; mathematically it is the proof
  of the implication from the descent statement to the criterion.

## Proof

`isFiniteOver_of_effectiveRefinements`: by definition, `g.IsFiniteOver V U`
consists of `g.baseMap '' V ⊆ U` (the hypothesis `hVU`) and, for every
recognized target affinoid `W` with `W.locus ⊆ U`, a recognized source
affinoid with locus `V ∩ g⁻¹(W.locus)`, the chart-range inclusion, and finite
Banach `g.fullRecognitionPairs.pullback`. For such `W`, take the family
refinement `F := hfam.refinement W hWU`, the Hausdorffness of
`V ∩ g⁻¹(W.locus)` from `t2Space_inter_preimage_locus_of_targetFamilies`, and a
chosen effective realization `P := (hreal W F).some`. With that
Hausdorffness instance in context, the recognition module supplies the witness
`⟨F.preimage P, F.preimage_admissible P, F.preimage_locus P,
F.pullback_isFiniteBanach P⟩`.

`finiteOverTargetLocality_of_descent`: given the data of the statement, the
family hypothesis of `FiniteOverTargetLocalityStatement` is definitionally
`g.HasFiniteTargetFamilies V U`. The effective realization for a refinement
`F` of `W` is `hdesc K W.algebra F.models.rightCover.cover
F.models.descentLocalAlgebras F.models.algebraDescentData`, i.e. descent along
the finite full-domain cover of `W` underlying the refinement, with the local
finite algebras and overlap data of the models. The openness hypotheses of the
statement are not needed.
