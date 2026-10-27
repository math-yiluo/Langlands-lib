# Cross-universe transport of whole-Levi standard modules and weak quotients

Author: Worker 735.

This module is internal implementation infrastructure. Every construction in it
is a composition of published Library equivalences, intertwiners and transport
laws. It is not attributed to a theorem in the literature, and it proves no
uniqueness, recovery or classification statement.

## Setting and universes

Fix a p-adic field `F : PadicField.{uF} p` with topological data `T`, a rank
`n`, and an ordered block shape `B : GeneralLinear.BlockShape n`. Let
`A i : SmoothRep.{0, uF, uV}` be smooth representations of `GL_{B.size i}(F)`.
The universes `uF` (field), `uV` (block carriers), `uJ` (quotient carrier) and
`uX` (auxiliary) stay independent. The common carrier universe is
`max uF uV uJ uX`. Each declaration takes the four universes explicitly as
`.{uF, uV, uJ, uX}`. `quotientLiftIso` also takes `uW` and `uK`. No positivity
of `n` or of the block sizes is used beyond what `BlockShape` already contains.
The checkUnivs linter is switched off for `liftedBlocks`, `liftedDatum` and
`quotientLift`. Some of their universes occur only inside this joint maximum,
and that is the intended design.

## Block lifts and tensor equivalences

- `liftedBlocks T B A i` is `SmoothRep.universeLift.{max uF uJ uX} (A i)`. Its
  carrier is `ULift (A i)` in `max uF uV uJ uX`, and its action is
  `universeLiftRepresentation` of the original one
  (`liftedBlocks_representation`, by `rfl`).
- `blockLiftEquiv T B A i` is the published `SmoothRep.universeLiftEquiv`,
  which sends `v ↦ ULift.up v` (`blockLiftEquiv_apply`).
- Each lifted block is smooth because it is a bundled `SmoothRep`.
  Irreducibility and analytic temperedness are equivalent for `A i` and its
  lift. The proofs are the published `SmoothRep.isIrreducible_universeLift_iff`
  and `T.isTempered_universeLift_iff` (`liftedBlocks_isIrreducible_iff` and
  `liftedBlocks_isTempered_iff`).
- `tensorLiftEquiv T B A` is an actual representation equivalence from the
  untwisted block tensor `B.blockTensor (fun i => (A i).representation)` to the
  block tensor of the lifted factors. It is the published external tensor
  product of equivalences `FiniteTensorFiltration.externalCongr` applied to the
  factor lifts. On pure tensors it acts factorwise (`tensorLiftEquiv_tprod`).
- Take a whole-Levi representation `σ : Rep.{uV} ℂ (B.Levi F.Carrier)` and a
  *supplied* actual equivalence `eσ` from `σ.ρ` to the untwisted block tensor.
  Then `leviLiftEquiv T B A σ eσ` is `eσ.trans (tensorLiftEquiv T B A)`
  (`leviLiftEquiv_apply`).
- `isLeviTempered_liftedTensor_iff` shows that whole-Levi analytic temperedness
  `RelativeRegularComparison.IsLeviTempered` holds for `σ` exactly when it holds
  for the lifted tensor. The proof is the published
  `T.isLeviTempered_iff_of_equiv` applied to `leviLiftEquiv`. Neither direction
  is assumed.

## Lifted datum and standard module

Assume each `A i` is irreducible and analytically tempered, and let `t` be a
strictly decreasing real vector. Then `liftedDatum T B A hA hT t ht` is a
`T.TemperedLanglandsDatum.{max uF uV uJ uX, uF} n`. Its shape is `B`, its
blocks are `liftedBlocks T B A`, and its exponent is `t`. All three hold by
`rfl` (`liftedDatum_shape`, `liftedDatum_blocks` and `liftedDatum_exponent`).
Its irreducibility and temperedness fields come from the lifted-block
equivalences above.

`standardModuleEquiv T B A hA hT t ht σ eσ` is an actual representation
equivalence from `(liftedDatum …).standardModule.representation` to
`T.normalizedParabolicInduced B (T.leviRealPowerTwist B t σ.ρ)`. It composes
two published equivalences:

1. `RegularHeadExistence.standardModuleLeviTwistEquiv`. This identifies the
   standard module with normalized induction of the real twist of the lifted
   untwisted tensor.
2. `T.normalizedParabolicInducedEquiv B` applied to
   `twistEquiv (T.leviRealPowerCharacter B t) (leviLiftEquiv T B A σ eσ).symm`.
   This twists the inverse of the lifted factorization by the real Levi
   character and then induces it.

Pointwise, `standardModuleEquiv_eval` states that for each function `f` in the
standard module and each `g`, the value of the image at `g` is
`(leviLiftEquiv T B A σ eσ).symm` applied to the value of `f` at `g`. This holds
by `rfl`.

## Weak quotients and their lifts

Let `J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier)` be arbitrary.

- `isSmooth_of_surjective_induced` shows that `J.ρ` is smooth whenever there is
  a surjective intertwiner `q` onto it from any normalized parabolic induction
  `T.normalizedParabolicInduced B ρ`. The proof is the published
  `isSmooth_of_surjective` together with
  `T.isSmooth_normalizedParabolicInduced`.
- `quotientLift T J hJ` takes any smoothness proof `hJ` and returns
  `SmoothRep.universeLift.{max uF uV uX} (SmoothRep.of J.ρ hJ)`, with carrier
  universe `max uF uV uJ uX`. `quotientLiftEquiv` is the lift `v ↦ ULift.up v`
  (`quotientLiftEquiv_apply`). Irreducibility is equivalent for `J` and its
  lift (`quotientLift_isIrreducible_iff`). No admissibility of `J` is assumed.
- Take `J : Rep.{uJ}` and `K : Rep.{uK}` together with an actual equivalence
  `e : J.ρ.Equiv K.ρ`. Then `quotientLiftIso T J K hJ hK e` is an isomorphism
  `quotientLift.{uF, uV, uJ, max uW uK uX} T J hJ ≅ quotientLift.{uF, uW, uK, max uV uJ uX} T K hK`
  in the smooth category. Both carriers lie in `max uF uV uW uJ uK uX`. The
  isomorphism is `SmoothRep.mkIso` of the composite `down`, then `e`, then
  `up`, and its forward map sends `up v ↦ up (e v)` (`quotientLiftIso_hom_apply`).

Now fix the data of the previous section and a surjective actual intertwiner
`q` from `T.normalizedParabolicInduced B (T.leviRealPowerTwist B t σ.ρ)` onto
`J.ρ`. Then:

- `quotientMap` is the intertwiner from the lifted standard module to
  `quotientLift T J (isSmooth_of_surjective_induced …)`. It is
  `quotientLiftEquiv ∘ q ∘ standardModuleEquiv`. Pointwise it sends
  `f ↦ ULift.up (q (standardModuleEquiv … f))` (`quotientMap_apply`, by `rfl`).
- `quotientMap_surjective` holds because a composite of two equivalences and
  the surjection `q` is surjective.
- `isLanglandsQuotient_quotientLift`: if `J` is irreducible, then the lifted
  `J` satisfies the existing weak relation
  `(liftedDatum …).IsLanglandsQuotient`. The witness is `quotientMap`.
- `isLanglandsQuotient_quotientLift_of_exists` is the same conclusion when only
  `∃ q, Function.Surjective q` is supplied, for any smoothness proof of `J`.

The quotient relation is the weak one: an irreducible target with some
surjective intertwiner. It chooses no head and asserts no uniqueness of the
quotient kernel.

## Limits

The factorization `eσ` of `σ.ρ` into tempered blocks is a hypothesis of the
adapter. Its existence, analytic tensor reflection, uniqueness of the Langlands
parameter and tensor recovery are not proved here and remain with their
separate owners. This module does not prove or assume
`Langlands.GLWholeLeviLanglandsRecoveryStatement`, and it does not import the
semistandard conjugacy statement.
