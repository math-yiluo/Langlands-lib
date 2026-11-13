# The special-torus model from a model containing bounded torus points

This module defines the proposition

`Langlands.Geometry.Building.SpecialTorusIntegralModelReductionStatement.{u} : Prop :=
  SpecialTorusBoundedModelStatement.{u} → SpecialTorusIntegralModelStatement.{u}`

and proves it as `specialTorusIntegralModelReductionStatement`. The proof is the theorem

`Langlands.Geometry.Building.specialTorusIntegralModelStatement_of_boundedModel :
  SpecialTorusBoundedModelStatement.{u} → SpecialTorusIntegralModelStatement.{u}`.

So the smooth integral model with special-torus data follows from a smooth model whose
base change to the maximal-unramified integers contains the maximal bounded subgroups of
two split tori. The remaining building input is the residual
`Langlands.Geometry.Building.SpecialTorusBoundedModelStatement`. The conclusion is the
Library statement `SpecialTorusIntegralModelStatement` unchanged. The proof uses neither
`SpecialTorusExistenceStatement`, `UnramifiedSpecialApartmentStatement` nor
`ValuationApartmentAxiomsExistenceStatement`; its only hypothesis is the residual.

Notation: `F` is a nonarchimedean local field, `K = inertiaFixedField F` its maximal
unramified extension, `O_K = fixedFieldIntegers F` the valuation ring of `K`, and
`v = MaximalUnramified.valuation F`. The Markdown of
`SpecialTorusBoundedModelStatement` explains how these match KP's `k`, `K`, `o`, `O`, `ω`
and `H(K)^1`.

## Auxiliary facts

In the namespace `Langlands.Geometry.Building.SpecialTorusIntegralModel`:

* `infinite_residueField_fixedFieldIntegers F`: the residue field of `O_K` is infinite. The
  published `MaximalUnramified.infinite_residueField` states this for the valuation ring
  of `v`. `MaximalUnramified.valuationSubring_eq` says that this ring is `O_K`.
* `valuation_units_eq_one F a`: for a unit `a` of `O_K`, `v a = 1`. Every element of `O_K`
  has `v ≤ 1`, by `MaximalUnramified.mem_valuationSubring_iff` and
  `Valuation.mem_valuationSubring_iff`. Mathlib's `Valuation.Integers.one_of_isUnit'` then
  gives `v a = 1`.

The module also declares local instances for the algebra structure of `O_K` over `𝒪[F]`
and the scalar tower `𝒪[F] → O_K → K`. These are the same terms as in
`Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent`, which uses them to define
`M.baseChangeUnramified`.

## The reduction

Take `F`, a connected reductive `G` and a maximal split torus `iS : S ⟶ G`. The hypothesis
gives a smooth model `M` with the two containments of
`SpecialTorusBoundedModelStatement`, and a maximal `K`-split torus `iA : A ⟶ G_K`. The
proof uses two facts about `O_K`: it is a discrete valuation ring
(`fixedFieldIntegersIsDVR_of_valuesFromBase` with `fixedFieldValuesFromBase`), hence
noetherian, and its residue field is infinite.

The theorem `IntegralModel.exists_connected_specialTorusModel` (module
`Langlands.GroupScheme.IntegralModel.SpecialTorusNeutralModel`) passes to the relative
identity component. It turns a smooth model with items 3 and 4 of
`SpecialTorusIntegralModelStatement` into a model with all four items. So it is enough to
prove items 3 and 4 for `M`.

* Item 3. Apply
  `IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_baseChange`
  with `R = 𝒪[F]`, `A = O_K`, `L = K`, the valuation `v` and `iT = iS`. The torus `S` is
  split and `iS` is closed because `iS` is a maximal split torus. The valuation hypothesis
  is `valuation_units_eq_one`. The intersection hypothesis is `F ∩ O_K = 𝒪[F]` inside `K`:
  an element `x : F` maps into `O_K` exactly when `x ∈ 𝒪[F]`. This is the published
  `IntegralModel.unramifiedIntegerRange_intersection`. The bounded-point hypothesis is
  item 2 of the residual statement.
* Item 4. Apply
  `IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded` to
  the model `M.baseChangeUnramified` over `O_K`, with the valuation `v` and `iT = iA`. The
  bounded-point hypothesis is item 3 of the residual statement. The result is a closed
  split `O_K`-torus `𝒜` with an isomorphism `e` of its generic fibre with `A` and generic
  map `CommGroupScheme.groupHom e.hom ≫ iA`. This map is a maximal split torus by the
  published `DatumTransport.isMaximalSplitTorus_torusIso_comp`.

## Comparison with Kaletha–Prasad

The decomposition follows the proof of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Proposition 9.3.4 (printed p.332 / PDF p.363). The model `M` plays the
role of KP's `𝒢^1_x`. KP take the schematic closure of `S` in `𝒢^1_x` and apply
Proposition B.2.4 (printed p.656 / PDF p.687). That proposition rests on Lemma B.2.3
(printed p.655 / PDF p.686), whose implication (1)⇒(2) uses the smoothening of an integral
model and a weight decomposition of its affine ring. The Lean route for split tori differs:

* It forms no schematic closure and uses no smoothening or smoothness of `M`. For a split
  torus `T ≅ 𝔾_m^I`, it constructs an integral homomorphism from the split torus
  `D_R(ℤ^I)` into the model directly (`SplitTorusClosure.exists_genericTorusMap_eq`). The
  coordinates of the universal point are Laurent polynomials, and their coefficients are
  shown integral by evaluating at integral units. This needs an infinite residue field of
  the valuation ring, which `O_K` has
  (`HopfPointIntegralClosure.coeff_mem_range_of_forall_evalUnits_mem`).
* It proves that this homomorphism is a closed immersion
  (`SplitTorusClosure.isClosedSubgroup_of_genericTorusMap`) because each coefficient ideal
  of a bialgebra map into a group algebra is idempotent, hence `0` or `1` over a noetherian
  domain (`HopfPointIntegralClosure.surjective_of_coeff_ne_zero`). This replaces KP's
  argument that `a_x² ∣ a_x` forces `a_x ∈ O^×`.
* The integral torus is `D_R(ℤ^I)` itself, so it is split by construction. KP's Lemma
  Proposition B.2.4 gives only an `o`-torus. The Markdown of `SpecialTorusIntegralModelStatement` adds
  a monodromy argument for its splitness; that argument is not needed here.
* For `S` over `𝒪[F]`, the hypothesis concerns `O_K`-points. The proof descends the Laurent
  coefficients from `O_K` to `𝒪[F]` with `F ∩ O_K = 𝒪[F]`. KP instead apply B.2.4 directly
  to the descended `o`-model.
* For `A` over `O_K`, the Library statement's Markdown uses Axiom 4.1.20(3). Here the
  closed split `O_K`-torus comes from the bounded points of `A`, by the same closure
  theorem.
* KP obtain the connected special fibre from the relative identity component `𝒢^0_x` of
  Axiom 4.1.20 and §9.2.5. Here it comes from the Library's smooth relative identity
  component, through `SpecialTorusNeutralModel`.

## Provenance

The proposition `SpecialTorusIntegralModelReductionStatement` is an internal bookkeeping
statement. Its hypothesis is the residual statement of this development, and its conclusion
is the Library statement `SpecialTorusIntegralModelStatement` unchanged. It records that the
target follows from the residual. The auxiliary facts about `O_K` are routine bookkeeping
from published Library results.

The module was drafted by Worker 5707 for Task 5707
(`f502c3c7-c095-4c74-bf82-ad8ffb916f57`, shared draft revision 2). Worker 88 wrote the
modules `RelativeComponentConstruction` and `SpecialTorusNeutralModel` that it uses. Worker
25 revised this Markdown for publication.
