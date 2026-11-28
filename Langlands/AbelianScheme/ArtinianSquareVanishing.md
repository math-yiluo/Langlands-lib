# The obstruction of the charts of an abelian scheme is a coboundary

Module `Langlands.AbelianScheme.ArtinianSquareVanishing` (namespace
`Langlands.AbelianScheme.ArtinianConstantCharts.Setting`).

In the setting of `ArtinianConstantCharts`, let `B` be an abelian scheme over `Spec R`, `C` the
constant abelian scheme over `Spec R'`, and assume `R`, `R'` Artinian and local.

## The special fibre of the constant scheme

- `Cres` is the base change of `C` to the field `R' / m'`. The reductions `Fres` and `F₂res` of `C`
  and `C × C` modulo `m'` use `Reduction.pullback` and `Reduction.fibreProduct`. Their objects in
  the category of schemes over the residue field are the underlying objects of `Cres` and its
  fibre square.
- `map_mul_reduction` identifies the reduction of `fst * snd` for `C` with multiplication on
  `Cres` by the multiplicative comparison `GroupScheme.baseChangePointsEquiv`.
- `appLE_hom_congr` and `appLE_hom_comp` give equality and composition rules for pulling back
  sections to smaller opens.

## Covers

Let `K : S.Charts B` be the finite affine cover of `B` with the constant chart identifications,
and let `D` lift its transition maps. Pulling back the covering condition gives `iSup_V` on
`C` and `iSup_cover` on its special fibre. On the special fibre of `C × C`, the product opens,
the sheared product opens and their union are covers (`iSup_cover_inl`, `iSup_cover_inr`,
`iSup_cover_square`). The product cover refines the inverse-image cover along `fst`. The
sheared product cover refines the inverse-image covers along multiplication and `snd`
(`cover_inl_le_fst`, `cover_inr_le_mul`, `cover_inr_le_snd`).

## Vanishing

Assume `maximalIdeal R' * ker φ = 0` and fix difference coordinates `b` for the target `C` and
the ideal `ker φ`.

- `obsB` is the obstruction cocycle of `D` and `obsSq` that of `Charts.squareLifts D` through the
  first projection (module `TransitionObstructionCech`).
- `refine_obsSq_inl` identifies the restriction of `obsSq` to the product charts with the
  pullback of `obsB` along `fst`.
- `refine_obsSq_inr` identifies its restriction to the sheared product charts with the pullback
  of `obsB` along multiplication minus its pullback along `snd`. Both restriction identities
  follow from `ArtinianSquareObstruction` by evaluating Čech cochains on tuples.
- `exists_coboundary` gives a degree-one cochain on the original residue cover with coboundary
  `obsB j` for each `j`, by `PrimitiveCechVanishing.exists_coboundary_tensor` applied to `Cres`.
- `Charts.nonempty_liftedTransitions_of_elementary` constructs `Nonempty K.LiftedTransitions`.
  It chooses lifts with diagonal inclusions (`exists_lifts`), chooses `Coordinates.ofTarget`,
  and uses the degree-one cochains above to correct the transitions by
  `Charts.nonempty_liftedTransitions` (module `ArtinianAbelianCharts`).

## Provenance

The product and shear comparison comes from Kai-Wen Lan's proof of Proposition 2.2.4.1
(*Arithmetic compactifications of PEL-type Shimura varieties*, Harvard thesis revised
14 March 2021, printed pp. 152–154, PDF pp. 180–182). In the Lean proof the two restrictions of
`obsSq` give `pr₁^* o = m^* o - pr₂^* o` in cohomology for each coordinate of the obstruction class
`o`. The primitive-class criterion then gives the vanishing needed for the correction of
SGA 1, Exposé III, Théorème 6.3 (recomposed edition, arXiv math/0206203v2, printed p. 66,
PDF p. 82).
