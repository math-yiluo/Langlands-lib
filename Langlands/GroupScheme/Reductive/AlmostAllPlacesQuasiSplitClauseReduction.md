# Quasi-splitness at almost all places from henselian quasi-splitness

Worker 62.

This module states and proves that the quasi-splitness clause of the published
[`AlmostAllPlacesQuasiSplitStatement`](AlmostAllPlacesQuasiSplitStatement.md) follows from
the published, not yet proved,
[`HenselianFiniteResidueQuasiSplitStatement`](../RelativeLevi/HenselianQuasiSplitStatement.md).
It does not prove the torsor clause, and it adds no axioms.

## Statement

`Langlands.GroupScheme.AlmostAllPlacesQuasiSplitClauseReductionStatement.{u} : Prop` is the
implication: if `HenselianFiniteResidueQuasiSplitStatement.{u}` holds, then for every number
field `F : Type u` and every group scheme `G` over `Spec F` with `IsConnectedReductive G`,
for all but finitely many `v : FinitePlace F` (the filter `Filter.cofinite`) the base change
of `G` along `Spec.map (CommRingCat.ofHom (algebraMap F (FiniteCompletion F v)))` satisfies
`IsQuasiSplit`. The conclusion is word for word the first conjunct of
`AlmostAllPlacesQuasiSplitStatement`.

The hypothesis `HenselianFiniteResidueQuasiSplitStatement` says that a reductive group scheme
(`IsReductive`) over the spectrum of a henselian local ring with finite residue field is
quasi-split over the base (`IsRelativeQuasiSplit`, Conrad's Definition 5.2.10: it has a
Borel subgroup over the base), together with a splitting over a finite étale local extension
that this module does not use.

## Theorems

- `AlmostAllPlacesQuasiSplitReduction.henselianLocalRing_adicCompletionIntegers F v`: the
  completed integer ring `v.adicCompletionIntegers F` is a henselian local ring. It is the
  published `adicCompletionIntegers_henselian (𝓞 F) F v`.
- `AlmostAllPlacesQuasiSplitReduction.eventually_isQuasiSplit F hH G hG`: the quasi-splitness
  clause for the given `F` and `G`, from `hH : HenselianFiniteResidueQuasiSplitStatement`.
- `almostAllPlacesQuasiSplitClauseReduction :
  AlmostAllPlacesQuasiSplitClauseReductionStatement.{u}`.

## Proof

This follows the hint to Conrad, *Reductive group schemes* (2014), Exercise 5.5.3(iii),
pp.182–183 (registered as `conrad-2014-reductive-group-schemes`): spread `G` out to a
reductive group scheme over a dense open subscheme of `Spec 𝓞_F` (part (i)), then pass from
the henselian local ring `𝓞_{F_v}` to its fraction field `F_v` (part (ii)).

1. `D := reductiveModelData F genericReductivitySpreading G hG`
   (`IntegralModel.ArithmeticReductiveSpreading`, with the published proof
   `genericReductivitySpreading` of `GenericReductivitySpreadingStatement`) is a finite set
   `D.places` of finite places, an integral model `D.model` of `G` over the ring of
   `D.places`-integers, and a proof `D.reductive` that `D.model.group` is reductive.
2. The exceptional set `{v | ¬ IsQuasiSplit …}` is shown to lie in the finite set
   `D.places`. Fix `v ∉ D.places`. The model
   `N := IntegralModelCompletions.model F D.places ⟨v, _⟩ D.model`
   (`Global.IntegralModelCompletions`) is an integral model of the base change `G_{F_v}` over
   `v.adicCompletionIntegers F`. Its group is the base change of `D.model.group` along the
   completion map of integer rings, so it is reductive by `IsReductive.baseChange`.
3. `v.adicCompletionIntegers F` is a henselian local ring (above), and its residue field is
   finite (the published instance `CompletionResidue.finite_adicResidueField`). The
   hypothesis therefore gives `IsRelativeQuasiSplit N.group`, hence a group scheme `B`
   over `Spec 𝓞_{F_v}` and a homomorphism `i : B ⟶ N.group` with `IsRelativeBorelSubgroup i`.
4. `IsRelativeBorelSubgroup.fieldPoint` (`RelativeLevi.BorelTransport`), applied at the
   field-valued point `Spec F_v ⟶ Spec 𝓞_{F_v}`, says that the base change of `i` to the
   generic fibre `N.genericFibre` satisfies `IsGeometricBorelSubgroup`. The generic fibre is
   connected reductive by `IsReductive.isConnectedReductive_algebraMap`, so
   `IsQuasiSplit N.genericFibre` holds.
5. `IsQuasiSplit.of_iso` along the model's generic isomorphism `N.genericIso` (between
   `N.genericFibre` and `G_{F_v}`) gives `IsQuasiSplit G_{F_v}`.

## Provenance

This is an internal reduction for Task 6635 (proof of `AlmostAllPlacesQuasiSplitStatement`).
Its hypothesis and conclusion are published statements. The torsor clause of the target is
handled separately, and the final proof combines the two clauses.
