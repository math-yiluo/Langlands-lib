# Generic split tori of the maximal unramified base change of a good model

Lean module: `Langlands.GroupScheme.IntegralModel.UnramifiedGenericSplitTorus`.

This module proves two facts about a split torus `i : 𝔾_m^I → 𝒢` of an integral model
`𝒢` over a valuation ring `R` with fraction field `K`, read on the generic fibre through
`IntegralModel.genericSplitTorusHom i : 𝔾_m^I_K → G`. They are the torus integrality input and
the Iwasawa factorization input of the split integral pinning that `M.baseChangeUnramified`
(the base change of a good model `M` to the integers of the maximal unramified extension
`L = inertiaFixedField F`) needs for the unramified special-stabilizer identity
`UnramifiedSpecialStabilizerStatement` (Bruhat–Tits II, Propositions 4.6.28(i), 4.6.29(i),
4.6.31).

## Provenance

All results are internal helper lemmas for the proof of that statement. They do not formalize a
numbered result of a source. Mathematically, the first theorem is the familiar fact that the
maximal bounded subgroup of a split torus `T(L)` consists of the points whose coordinates are
units of `𝒪_L`; here it is stated in the form used by
`SplitIntegralPinning.ofRootParametrizations` (field `hK_torus`). The second is the integral
Iwasawa decomposition `G(L) = 𝒢(𝒪_L) · P_G(λ)(L)`, already in the Library as
`HenselianParabolicCovering.baseChangeUnramified_exists_integral_mul_parabolic` for cocharacters
that come from integral ones. Here it is extended to every cocharacter of a generic split torus.

## Coordinate torus lemmas (namespace `Langlands.Geometry.Building.SplitIntegralPinning`)

Here `k` is a field, `I` a finite type, and `coordTorus k I` the split torus `𝔾_m^I` over `k`.

* `eq_pointsEquiv_symm_torusCharEval t`: a `k`-point `t` of the coordinate torus is the point
  whose `j`-th coordinate is the value `torusCharEval (proj j) t ∈ kˣ` of the `j`-th coordinate
  character, read as a global unit of `Spec k`. Proof: compare coordinates with `pointsEquiv`;
  `splitTorus.comp_proj` and `ChevalleyRootFamily.charValue_eq_rationalCharacterEval` identify
  both sides.
* `eval_centralizerValuation_id v t a`: let `w ∈ V(T) = X_*(T) ⊗ ℝ` be the real valuation
  vector of `t`, that is,
  `IntegerValuation.centralizerValuation v (𝟙 _) (restrictionEvaluation_id_bijective _) t`.
  Then the evaluation of `w` at a character `a` is the order
  `IntegerValuation.order v (a(t))`. This is `IntegerValuation.centralizerValuation_spec`
  for the identity map. Restriction of characters along the identity is the identity.
* `valuation_coordinate_eq_one_of_eval_eq_zero v t ht j`: if that valuation vector is zero,
  then every coordinate of `t` has valuation one. Proof: the kernel of the centralizer
  valuation is `characterValuationKernel` (`IntegerValuation.centralizerValuation_ker`), and
  coordinate characters are rational characters.

## General integral model lemmas (namespace `Langlands.GroupScheme.IntegralModel`)

Here `R` is a domain with fraction field `K`, `M : IntegralModel R K G`, and `I` is finite.

* `baseChangeCocharacter_exponentCocharacter_comp M i n`: for
  `i : splitTorus (Spec R) I ⟶ M.group` and `n : I → ℤ`, the generic fibre of the integral
  cocharacter `exponentCocharacter n ≫ i`, followed by `M.genericIso`, equals
  `exponentCocharacter n ≫ M.genericSplitTorusHom i`. Proof:
  `LocalRootGroup.baseChangeCocharacter_groupHom_comp` and the definitions of
  `genericSplitTorusHom` and `genericHom`.
* `exists_units_map_eq_of_valuation_eq_one hv c hc`: suppose that
  `v c ≤ 1 ↔ c ∈ range (algebraMap R K)` for all `c` (`R` is the valuation ring of `v`). Then
  every `c ∈ Kˣ` with `v c = 1` is the image of a unit of `R`. Proof: `c = r` and `c⁻¹ = r'`
  for some `r, r' ∈ R`; injectivity of `R → K` gives `r r' = 1`.
* `map_genericSplitTorusHom_mem_integralPoints hv hG i hi hsplit t ht hk`
  (**integrality on a generic split torus**). Assume:
  * `R` is the valuation ring of `v` (as above);
  * `G` is connected reductive;
  * `i` is a closed subgroup (`IsClosedSubgroup i`);
  * the generic split torus `i_K := M.genericSplitTorusHom i` is a maximal split torus of `G`.

  Let `t` be a `K`-point of `𝔾_m^I` such that every relative root `a` of `i_K` has
  `order v (a(t)) = 0`, and such that `i_K(t)` lies in `G(K)^1 = characterValuationKernel v G`.
  Then `i_K(t)` is an integral point of `M`.

  Proof: let `w` be the real valuation vector of `t`. By `eval_centralizerValuation_id`,
  `w` is killed by every relative root (hypothesis `ht`). It is also killed by the restriction
  to `i_K` of every rational character `χ` of `G`, because
  `χ(i_K(t))` has valuation one (hypothesis `hk`, via
  `rationalCharacterEval_characterRestrict`). Relative roots and restricted characters span
  the rational character space, so
  `eq_zero_of_eval_relativeRoots_of_eval_torusCharacterRestrict` gives `w = 0`. Then every
  coordinate of `t` has valuation one, hence is a unit of `R`, and
  `genericSplitTorusValue_mem_integralPoints_iff` (with `eq_pointsEquiv_symm_torusCharEval`)
  shows that `i_K(t)` is integral.

## Maximal unramified specializations

Here `F` is a non-archimedean local field, `G` an affine group over `F`, `M` an integral model of
`G` over `𝒪_F`, `L = inertiaFixedField F` with integers `fixedFieldIntegers F`, and
`v = MaximalUnramified.valuation F` the normalized valuation of `L`.

* `MaximalUnramified.valuation_le_one_iff_mem_range c`:
  `v c ≤ 1 ↔ c ∈ range (fixedFieldIntegers F → L)`. This follows from
  `MaximalUnramified.valuationSubring_eq`.
* `baseChangeUnramified_map_genericSplitTorusHom_mem_integralPoints hGL i hi hsplit t ht hk`:
  this is `map_genericSplitTorusHom_mem_integralPoints` for `M.baseChangeUnramified` and `v`,
  with `hGL : IsConnectedReductive (baseChanged F L G)`. With `K := M.baseChangeUnramified.integralPoints`
  it is exactly the field `hK_torus` of `SplitIntegralPinning.ofRootParametrizations`.
* `baseChangeUnramified_exists_integral_mul_parabolic_genericSplitTorus hG hSpecial i ν g`
  (**integral Iwasawa factorization for generic split tori**). Assume that `G` is connected
  reductive and that the special fibre of `M` is connected reductive. Let `i` be any split
  torus `𝔾_m^I → M.baseChangeUnramified.group` over `fixedFieldIntegers F`, and let `ν` be any
  cocharacter of the coordinate torus over `L`. Then every `g ∈ G(L)` is `κ * p`, where `κ`
  is in `M.baseChangeUnramified.integralPoints` and `p ∈ P_G(λ)(L)`, the `L`-points of the
  dynamic parabolic of `λ = ν ≫ M.baseChangeUnramified.genericSplitTorusHom i`.

  Proof: over a field every cocharacter of `𝔾_m^I` is `exponentCocharacter n` with
  `n = cocharacterLatticeEquiv L I ν`
  (`splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm`). By
  `baseChangeCocharacter_exponentCocharacter_comp`, `λ` is the generic fibre of the integral
  cocharacter `exponentCocharacter n ≫ i`, so
  `HenselianParabolicCovering.baseChangeUnramified_exists_integral_mul_parabolic` applies.

The file has a private instance: `IsAffineHom` for the structure morphism of
`baseChanged F L G`, the pullback of an affine morphism. It is used to state the relative
roots in the specialization. The Library statement module declares the same instance.
