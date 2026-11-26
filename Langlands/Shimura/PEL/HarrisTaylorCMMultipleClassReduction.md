# Pointed restriction of normalized Harris classes from lifts up to a multiple

All declarations are in `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The module
generalizes `classBaseChange_surjective_of_normalizedPolarizedActionLifts`
(module `HarrisTaylorCMArtinianClassReduction`) in two ways: the polarizations may
correspond up to a rational multiple, and lifts are asked only for the
representatives of the lower classes at one fixed Harris level.

## The multiplier condition

`PositivePolarizedActionReductionMultiple b X Y q e` concerns a morphism
`b : T ⟶ S` of quasi-separated schemes, positive polarized actions `X` over `S` and
`Y` over `T`, a rational unit `q : ℚˣ` and an equivariant rational isomorphism
`e : (RationalAlgebraAction.pullback b).obj X.actionObj ≅ Y.actionObj`. It asks, for
every constrained choice `W` of dual data on the restricted abelian scheme
(`PositivePullbackDualData … b X`), that the rational dual pullback of the
polarization of `Y` along `e` equal `q` times the canonical base change of the
polarization of `X` (`dualAbelianBaseChangeMap … X.polarization`, using the
published `dualAbelianBaseChange`). The equation is the Library's
`IsRationalDualPullbackMultiple` with multiplier `q`.

`positivePolarizedActionReductionMultiple_one_iff` records that the case `q = 1` is
exactly the published `PositivePolarizedActionIsometricReduction`.

## The reduction

`classBaseChange_surjective_of_levelMultipleLifts` fixes `b : T ⟶ S`, a structure
morphism `p : S ⟶ Spec F`, a field-valued point `t` of `T` with its composite
`t ≫ b`, the finite-fibre, torsion-unit, roots-of-unity, Lie-naturality and pair
additivity inputs of the existing class pullback `classBaseChange`, a choice of
pulled-back dual data, and a Harris level `U`. Its two hypotheses are:

- for every representative `x` of a lower class at `U` (an element of
  `HarrisLevelData … t … U` satisfying the normalized determinant condition and the
  numerical condition for `b ≫ p`) there are a positive polarized action `Y` over `S`
  satisfying both conditions for `p`, a unit `q` and an equivariant rational
  isomorphism `e` from the restriction of `Y` to `x.1` with
  `PositivePolarizedActionReductionMultiple … b Y x.1 q e`;
- the pointed fundamental-group map `fundamentalGroupMap b t (t ≫ b)` is surjective.

The conclusion is surjectivity of `classBaseChange … U`, the existing pointed
normalized class restriction at `U`.

The proof follows the multiplier-one proof. It chooses a representative `x` of a
lower class and its lift `Y`, `q`, `e`. An adelic frame of `x` transported back along
`e` and base change gives a frame on `Y` at `t ≫ b`, which is the input of
`framedPositiveActionBaseChange`. The multiplier condition for the chosen dual data
is the equation `PolarizedWeilLevel.Multiple … q e` between the changed action and
`x.1`, so it defines the level transport `PolarizedWeilLevel.levelIso` with
multiplier `q`. Surjectivity of the pointed monodromy map and
`framedPositiveActionTowerBaseChange_surjective` give a fixed orbit on `Y` whose
pullback is the preimage of the orbit of `x`. The class equality criterion
`HarrisNumericalWeilLevel.classOf_eq_iff`, which allows any rational unit as
multiplier, identifies the restriction of the resulting class with the class of `x`.

## Provenance

Internal. The module reuses the published frame transport, framed base change,
fixed-orbit surjectivity, level isogeny transport and class equality criterion,
and replaces the multiplier one of the Artinian reduction by an arbitrary rational
unit.
