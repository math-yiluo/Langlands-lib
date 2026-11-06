# Adelic points of Weil restrictions of algebraic spaces

Author: Worker 105.

`AdelicSpaceWeilRestrictionStatement` states Proposition 5.14 of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.20, for global
fields of both characteristics. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only states
the proposition and contains no proof.

Conrad writes on printed p.20: "Proposition 5.14. Let `F′/F` be a finite extension of global
fields, and `X′` a separated algebraic space of finite type over `F′`. For the separated
algebraic space `X = Res_{F′/F}(X′)` of finite type over `F`, the bijection of sets
`X(A_F) = X′(A_{F′})` is a homeomorphism." His proof reduces to the local fields and applies
Proposition 5.11(1).

## Objects

- `ringWeilRestriction`, `ringWeilRestrictionSpace` and `ringWeilRestrictionPointsEquiv` (from
  `Langlands/AlgebraicGeometry/AlgebraicSpace/SpaceWeilRestriction.lean`): the Weil restriction
  of fppf sheaves along `Spec F′ → Spec F`, the algebraic space it defines given a proof `h`
  that it is one, and the identification `Res_{F′/F}(X′)(A) = X′(F′ ⊗[F] A)` of points.
- `curvePlaceAdeleTensorMap` and `numberFieldAdeleTensorMap` (from
  `Langlands/Global/AdelicTensorBaseChange.lean`): the canonical `F′`-algebra map
  `F′ ⊗[F] A_F → A_{F′}`, `a ⊗ x ↦ a · ι(x)`.
- `curvePlaceSpaceSpreadTopology` and `numberFieldSpaceSpreadTopology` (from
  `Langlands/Global/AdelicSpacePointTopology.lean`): the topology on the adelic points of an
  algebraic space over the field attached to a model `X` over a ring of `S`-integers and an
  isomorphism `e` from the generic fibre of `X` to the space.
- `IsSeparated` (from `Langlands/AlgebraicGeometry/AlgebraicSpace/RingPoints.lean`) and
  `FiniteTypeOverRing` (from `Langlands/Global/AdelicSpaceLevelPointsStatement.lean`) express
  "separated of finite type".

## The statements

The comparison map sends an adelic point `x` of `Res_{F′/F}(X′)` to
`RingPoints.changeRing (tensor map) (ringWeilRestrictionPointsEquiv … x)`: identify `x` with an
`F′ ⊗[F] A_F`-point of `X′`, then change coefficients along `F′ ⊗[F] A_F → A_{F′}`. This is
Conrad's bijection `X(A_F) = X′(A_{F′})`.

- `NumberFieldSpaceWeilRestrictionStatement`: let `K'/K` be an extension of number fields
  (`Algebra K K'`) and `Y'` a separated algebraic space of finite type over `Spec K'`. Then
  there is a proof `h` that the Weil restriction of `Y'` is an algebraic space, the algebraic
  space `ringWeilRestrictionSpace K K' Y' h` is separated and of finite type over `K`, and the
  following holds. For all finite sets `S`, `S'` of finite places of `K`, `K'`, separated
  models `X`, `X'` of finite type over the `S`-integers and `S'`-integers, and isomorphisms
  `e` from the generic fibre of `X` to the Weil restriction and `e'` from the generic fibre of
  `X'` to `Y'`, the comparison map is a homeomorphism (`IsHomeomorph`). Its source carries the
  topology attached to `(S, X, e)` and its target the topology attached to `(S', X', e')`.
- `CurvePlaceSpaceWeilRestrictionStatement`: the same for a finite field `k`, function fields
  `F`, `F'` over `k` (each with its `RatFunc k`-algebra structure), an extension `F → F'`
  compatible with `k` and finite-dimensional, and nonempty finite sets of places `S`, `S'`.
- `AdelicSpaceWeilRestrictionStatement` is the conjunction of the two, in a common universe.

## Relation to the source and derived content

Conrad's proposition presupposes Lemma 5.10: the Weil restriction is a separated algebraic
space of finite type. The statement asserts this together with the homeomorphism, as the
published Proposition 5.11(1) statement does. Any two proofs `h` are equal, so the existential
form says exactly that the Weil restriction is such a space and that the map is a
homeomorphism.

Conrad's topologies on `X(A_F)` and `X′(A_{F′})` are defined through models over rings of
`S`-integers. The statement quantifies over all separated models of finite type and all
generic-fibre isomorphisms on both sides, so the homeomorphism holds for every choice of
models. Independence of the topology from the model, and existence of models, are separate
claims (stated in `AdelicSpacePointTopologyStatement`) and are not needed for this
formulation.

The homeomorphism includes bijectivity of the comparison map. Bijectivity would follow from
the tensor decomposition `F′ ⊗[F] A_F ≅ A_{F′}`, which is not stated separately here.

No separability is assumed for `F'/F`, as in Conrad. For number fields, `K'` is automatically
finite over `K`. Conrad's conventions for global fields are used: function fields have a
finite constant field, and model sets `S` are nonempty for function fields. These are the
conventions of the published `AdelicSpaceLevelPointsStatement`.

Also derived here: the names, the packaging of the two characteristics, and the formulation
of the bijection through the point identification and the tensor map.
