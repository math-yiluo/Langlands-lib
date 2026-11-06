# Proof that full adelic representation heights are continuous and proper

Author: Worker 1518.

`Langlands.Global.RepresentationGrowth.adelicRepresentationHeightProperness`
proves `AdelicRepresentationHeightPropernessStatement` in universe `u`. Fix a
number field `F`, an affine group scheme `G` over `Spec F`, a rank `N > 0` and a
matrix representation `rho`. The function `adelicHeight F G rho` is continuous on
`AdelicGroupPoints F G`. If `GroupScheme.IsClosedSubgroup rho` holds, it is also an
`IsProperMap`. No other hypothesis is used.

The proof has two steps. It first proves both properties for the standard full
adelic matrix height `AdelicMatrixHeight.height F n` on `AdelicGL F n` at positive
rank `n`. It then pulls them back along the existing continuous homomorphism
`adelicMatrix F G rho`, since `adelicHeight F G rho` is by definition
`height F N ∘ adelicMatrix F G rho`. The norms are the existing ones from
`AdelicRepresentationHeight`: the normalized finite-completion norms, and the
infinite factors `(n * infiniteLocal v) ^ v.mult`. Getz and Hahn, *An
Introduction to Automorphic Representations* (2024), (6.3)–(6.4) and (6.7)–(6.8),
are cited only for these conventions. As the statement Markdown explains, the
properness assertion itself is derived internally and is not a result of that
source.

## Continuity of the matrix height

`continuous_finiteLocal` and `continuous_infiniteLocal`: for each place `v`, the
local factor `g ↦ finiteLocal F n g v` (or `infiniteLocal`) is continuous. It is
the maximum of the sup norm of the projected matrix of `g` and that of `g⁻¹`.
The projections `finiteProjection F v` and `infiniteProjection F v` are continuous,
and on the units topology both `g ↦ g` and `g ↦ g⁻¹` are continuous into matrices
(`Units.continuous_val`, `Units.continuous_coe_inv`). `continuous_entry` and
`continuous_inv_entry` record the entry maps `g ↦ g i j` and `g ↦ g⁻¹ i j`.

`integralAway F n S`, for a set `S` of finite places, is the set of `g` such that,
at every finite place `v ∉ S`, every entry of `g` and of `g⁻¹` has finite
component in the integer ring `v.adicCompletionIntegers F`.
`isOpen_integralAway` shows that it is open. The set of finite adeles that are
integral at every place outside `S` is open in the restricted-product topology
(Mathlib's `RestrictedProduct.isOpen_forall_imp_mem`, using that each integer
ring is open). So `integralAway F n S` is a finite intersection of preimages of
this open set under the continuous maps sending `g` to the finite component of an
entry of `g` or `g⁻¹`.

`finiteLocal_eq_one`: at positive rank, if every entry of `g` and `g⁻¹` is
integral at `v`, then `finiteLocal F n g v = 1`. Integral elements have norm at
most one, so the factor is at most one. The published `one_le_finiteLocal` gives
the reverse inequality.

`continuous_finiteProduct`: the finite-place product
`g ↦ ∏ᶠ v, finiteLocal F n g v` is continuous. We prove continuity at each `g₀`.
The entries of `g₀` and `g₀⁻¹` are integral at all but finitely many finite
places, because they are restricted-product elements. Let `S` be the finite set
of exceptional places. Then `g₀` lies in the open set `integralAway F n S`. By
`finiteLocal_eq_one`, every `g` in this set has its finite product equal to the
fixed finite product `∏ v ∈ S, finiteLocal F n g v`
(`finprod_eq_prod_of_mulSupport_subset`). That fixed product is continuous, and
the two functions agree on a neighbourhood of `g₀`. So the support is controlled
uniformly on a neighbourhood, not only at each point.

`continuous_height`: at positive rank, `height F n` is continuous. It is the
product of a finite product over infinite places of continuous functions with the
continuous finite-place product.

## Local estimates

`mem_adicCompletionIntegers_iff_norm_le_one`: an element of a finite completion
is integral exactly when its normalized norm is at most one.

`absNorm_le_norm_of_one_lt`: if `‖x‖ > 1` in the completion at a finite place
`v`, then `Ideal.absNorm v.asIdeal ≤ ‖x‖`. By Mathlib's
`NumberField.FinitePlace.norm_def`, the norm of a nonzero `x` is
`(absNorm v.asIdeal) ^ k`, where `k` is the integer exponent of its valuation in
`ℤᵐ⁰` (`WithZeroMulInt.toNNReal_neg_apply`). The condition `‖x‖ > 1` means
that the valuation exceeds one, so `k ≥ 1`. Since `absNorm v.asIdeal > 1`, the
power is at least the absolute norm itself. This follows the proof of Mathlib's
`FinitePlace.two_le_norm_of_one_lt_norm`.

`finite_absNorm_le`: for each real `B`, only finitely many finite places have
`absNorm v.asIdeal ≤ B`. This is Mathlib's `Ideal.finite_setOfPred_absNorm_le`
for the bound `⌊B⌋₊`, pulled back along the injective map `v ↦ v.asIdeal`.

`isCompact_closedBall_finiteCompletion`: closed balls about zero in a finite
completion are compact. The published `isCompact_adicCompletionIntegers` says the
integer ring is a compact neighbourhood of zero, so the completion is locally
compact. A locally compact nontrivially normed field is a proper space
(`ProperSpace.of_locallyCompactSpace`).

`isCompact_closedBall_infiniteCompletion`: closed balls about zero in an infinite
completion are compact. The completion embeds isometrically in `ℂ` by
`InfinitePlace.Completion.extensionEmbedding`. This is a closed embedding, so a
closed ball is the preimage of a compact closed ball of `ℂ`.

## Compact boxes of adeles and matrices

`finiteBox F B` is the set of finite adeles `a` such that `‖a v‖ ≤ B` at every
finite place, and `a v` is integral whenever `B < absNorm v.asIdeal`.
`exists_isCompact_superset_finiteBox` shows that it lies in a compact set of
finite adeles. Let `T` be the set of places with `B < absNorm v.asIdeal`. By
`finite_absNorm_le`, its complement is finite, so the cofinite filter is finer
than the principal filter of `T`. Let `Q` be the product of the integer rings at
places of `T` and of the closed `B`-balls at the other places. By Tychonoff
(`isCompact_univ_pi`) and the two local compactness lemmas, `Q` is compact. For
the principal filter of `T`, the restricted product embeds into the full product
(`RestrictedProduct.isEmbedding_coe_of_principal`). Its range is the set of
families that are integral on `T` (`RestrictedProduct.range_coe_principal`), and
this range contains `Q`. So the preimage `P` of `Q` in that restricted product is
compact. The inclusion into the cofinite restricted product is continuous
(`RestrictedProduct.continuous_inclusion`). So the image of `P` is compact, and
it contains `finiteBox F B`.

`adeleBox F B` is the set of adeles whose infinite components have norm at most
`B` and whose finite part lies in `finiteBox F B`.
`exists_isCompact_superset_adeleBox` places it in the compact product of a
product of closed balls at the infinite places with the compact set above.

`entryBox F n E` is the set of `g` in `AdelicGL F n` such that every entry of `g`
and of `g⁻¹` lies in `E`. `isCompact_entryBox`: if `E` is compact, so is this
set. Matrices with all entries in `E` form a compact set by Tychonoff. Mathlib's
`Units.isClosedEmbedding_embedProduct` says that the map `g ↦ (g, op g⁻¹)` is a
closed embedding of the units into `M × Mᵐᵒᵖ` when `M` is a `T1` space with
continuous multiplication. Here `M` is the matrix ring over the adeles, which is
Hausdorff. The Hausdorff instances on the infinite adeles, finite adeles and
adeles are obtained from their product and restricted-product descriptions. The
entry condition is the preimage of the compact product of two such matrix sets,
so it is compact.

## Compact sublevel sets and properness of the matrix height

`sublevel_subset`: at positive rank, every `g` with `height F n g ≤ B` lies in
`entryBox F n (adeleBox F B)`. Every infinite factor `(n * infiniteLocal) ^ mult`
is at least one (`one_le_nat_mul_localMaximum`). Every finite factor is at least
one (`one_le_finiteLocal`). Hence the infinite product and the finite product are
each at least one and at most `B`. Each single factor is then at most `B`
(`Finset.prod_le_prod_of_subset_of_one_le₀`; for the finite product, use a
finite set containing `v` and the support from
`hasFiniteMulSupport_finiteLocal`). Since `n ≥ 1` and `mult ≥ 1`, this gives
`infiniteLocal F n g w ≤ B` at every infinite place and
`finiteLocal F n g v ≤ B` at every finite place. Each entry of `g` and `g⁻¹` is
bounded by the local factor (`entry_le_localMaximum`, with `localMaximum_inv` for
the inverse). So all its local norms are at most `B`. If such an entry were
nonintegral at a place with `B < absNorm v.asIdeal`, then
`absNorm_le_norm_of_one_lt` would give `absNorm v.asIdeal ≤ B`, a contradiction.
So every entry and inverse entry lies in `adeleBox F B`.

`isCompact_sublevel`: at positive rank, `{g | height F n g ≤ B}` is compact. It is
closed, by continuity of the height. It is contained in `entryBox F n E` for a
compact `E ⊇ adeleBox F B`, which is compact by `isCompact_entryBox`.

`isProperMap_height`: at positive rank, `height F n` is a proper map. We use
Mathlib's `isProperMap_iff_isCompact_preimage`, which applies because `ℝ` is
Hausdorff and locally compact, hence compactly generated. A compact `K ⊆ ℝ` is bounded above by some `B`. Its preimage
is closed and lies in the compact sublevel set for `B`, so it is compact.

## Pullback to the representation height

`continuous_adelicHeight`: `adelicHeight F G rho` is the composition of
`height F N` with the continuous `adelicMatrix F G rho`. So it is continuous for
every affine `G` and every representation, at positive rank `N`.

`isClosedEmbedding_adelicMatrix`: if `GroupScheme.IsClosedSubgroup rho` holds,
then `adelicMatrix F G rho` is a closed embedding. By definition, the premise says
that the underlying scheme morphism of `rho` is a closed immersion. The adele
ring is Hausdorff, so the published `GroupScheme.isClosedEmbedding_affinePointsTarget`
says that the induced map from the adelic points of `G` to the adelic points of
the general linear group scheme is a closed embedding. The general linear group
scheme is affine (`GroupScheme.GeneralLinear.isAffine_groupScheme`). Composing
with the published homeomorphism `GeneralLinearGroupPoints.adelicHomeomorph F N`
onto `AdelicGL F N` gives exactly `adelicMatrix F G rho`.

`isProperMap_adelicHeight`: under the same premise, `adelicHeight F G rho` is a
proper map. A closed embedding is a proper map, and a composition of proper maps
is proper (`IsProperMap.comp`).

`adelicRepresentationHeightProperness` assembles the two parts.
