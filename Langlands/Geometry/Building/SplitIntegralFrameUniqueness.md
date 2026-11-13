# Uniqueness of the fixed point of a split integral frame

Module `Langlands.Geometry.Building.SplitIntegralFrameUniqueness`. It applies the published
abstract uniqueness theorem `KPApartmentData.eq_apartmentMap_of_forall_smul_eq`
(`GenericSpecialFixedPoint`) to a published split integral frame
`F : B.SplitIntegralFrame` (`SplitIntegralFrame`). Here
`B : IntegerValuationBuildingData v G` over a field `k`, with
`v : Valuation k ℤₘ₀`. All hypotheses of the abstract theorem are produced inside the
proof, except the Iwasawa factorization and the choice of a regular unit.

## Declarations

Namespace `Langlands.Geometry.Building.IntegerValuationBuildingData`:

* `cocharacterPoints_mem_characterValuationKernel`: for a unit `c` with `v c = 1` and a
  cocharacter `ν` of `B.S`, the torus point `ν(c)` (the published
  `CocharacterUniformizer.cocharacterPoints`) lies in the common kernel of the character
  valuations of `B.S`.
* `cocharacterPoint B ν c` is the definition of this unit. It is the rational point
  `i(ν(c)) = rationalPoints.map B.i (cocharacterPoints k B.S ν c)` of `G`.
* `cocharacterPoint_eq_map_j`: it equals the image of `s(ν(c))` under the centralizer
  inclusion `j`, where `s` and `j` are the maps of `B.centralizer`.
* `cocharacterPoint_mem_centralizerPoints`: it lies in `centralizerPoints B.i`.
* `cocharacterPoint_smul_eq_self`: if `v c = 1`, then as a normalizer point it fixes every
  apartment point.

Namespace `IntegerValuationBuildingData.SplitIntegralFrame`, for a frame `F`:

* `cocharacterPoint_mem_K`: if `v c = 1`, then `cocharacterPoint B ν c ∈ F.K`.
* `order_eq_zero_of_valuation_eq_one` and `order_mul`: the order of a unit with
  valuation one is `0`, and the order is additive.
* `val_inv_mul_conj`: let `t` be a torus point and `b` a root with `v (b(t) - 1) = 1`. For
  `h ∈ U_b(k)` and every apartment point `z`, conjugation by `i(t)` followed by division
  keeps the value: `z.val b (h⁻¹ * (i(t) h i(t)⁻¹)) = z.val b h`.
* `eq_apartmentMap_of_forall_smul_eq`: the hypotheses are
  * `hk : ∃ d : kˣ, d ^ 2 ≠ 1`;
  * a point `x` at which every root value `F.rootValue x a` vanishes;
  * a generic cocharacter `ν` with the factorization `∀ g, ∃ κ ∈ F.K, ∃ p ∈ P_ν(k),
    g = κ * p`, where `P_ν = Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ B.i)`;
  * a unit `c` with `v c = 1` and `v (c ^ ⟨b, ν⟩ - 1) = 1` for every root `b` positive on
    `ν`.

  Under these hypotheses, every point of `B.ReducedBuilding` fixed by `F.K` equals
  `B.apartmentMap x`.
* `eq_apartmentMap_of_forall_smul_eq_of_infinite`: the same conclusion when the residue
  field of `v.valuationSubring` is infinite. Then `hk` and the unit `c` are no longer
  hypotheses.

## Implemented proof

*The torus element.* Put `t = ν(c)` and `s = cocharacterPoint B ν c`. By the published
`rationalCharacterEval_cocharacterPoints`, every character of `B.S` takes the value
`c ^ ⟨χ, ν⟩` at `t`, which has valuation one. So `t` lies in the kernel of the character
valuations of `B.S`. The published `map_mem_characterValuationKernel` moves this to
`s(t)` in the centralizer `Z`. The frame field `centralizer_mem_K` and the published
`map_mem_centralizerPoints` give `s ∈ F.K` and `s ∈ centralizerPoints B.i`. The published
`mem_characterValuationKernel_iff_smul_eq` shows that `s` fixes every apartment point.
The identification of `s` with `j(s(t))` is `coe_torusNormalizer`.

*Values.* Write `h = u_b(e)` (`u_surjective`). The frame field `torus_conj` gives
`i(t) u_b(e) i(t)⁻¹ = u_b(b(t) e)`, and `u_add` gives
`u_b(e)⁻¹ u_b(b(t) e) = u_b((b(t) - 1) e)`. For `e = 0` both sides are `1`. Otherwise
`(b(t) - 1) e` is a unit, and the published value formula `val_u` gives values
`ord((b(t) - 1) e) + rootValue = ord(e) + rootValue`, because `ord(b(t) - 1) = 0`. For
`t = ν(c)` and `b` positive, `b(t) = c ^ ⟨b, ν⟩` with a nonnegative exponent.

*Assembly.* The published `K_eq_oneStabilizer` shows that `F.K` fixes the image of `x`.
The depth-zero root groups at `x` lie in `B.sharpFixer {x}`, which lies in `F.K` by the
published `sharpFixer_le_K`. The root point `u_a(1)` has value `rootValue = 0` at `x`
(`val_u_one`). The relative roots are reduced by the frame field `two_smul_not_mem`. These
are exactly the remaining hypotheses of `eq_apartmentMap_of_forall_smul_eq` for
`B.apartment`.

*Infinite residue field.* The positive roots of `ν` are finite. The exponents
`⟨b, ν⟩.toNat` form a finite set of positive integers. `exists_unit_valuation_pow_sub_one_eq_one`
from `RegularUnitExistence` gives `c`, and `exists_unit_sq_ne_one` gives `d`.

## Provenance and scope

This is an internal assembly of published results. It realizes, for split integral
frames, the fixed-point uniqueness of Bruhat–Tits II, Proposition 4.6.28(i) and
Corollary 4.6.29(i), by the route of `GenericSpecialFixedPoint`; the Lean statements are
not quoted. The Iwasawa factorization remains a hypothesis. For integral models over the
maximal unramified extension it is supplied by `HenselianIwasawaFactorization`, once a
cocharacter of the model is related to `ν`; that relation is not proved here.
