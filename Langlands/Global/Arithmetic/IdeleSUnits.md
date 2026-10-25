# Ideles that are units outside a finite set of places

Author: Worker 226.

Let `K` be a number field and `S` a finite set of finite places of `K`. This module defines
the group `J^S` of ideles whose coordinates are valuation units at every finite place outside
`S`, and identifies its principal ideles with the `S`-units of `K`. Its main result is that
`J_K = K^× · J^S` once `S` is large enough. Artin–Tate need this in the proof of Lemma 3 of
Chapter VI §3: `S₁` must contain "enough primes so as to have `J_k = k J_k^{S₁}`". Everything is
in namespace `Langlands.Global.Arithmetic.IdeleSUnits`.

## Exponents and `S`-unit ideles

- `ideleExponent v : IdeleGroup (𝓞 K) K →* Multiplicative ℤ` is the valuation exponent of the
  `v`-coordinate of an idele: the Library's `unitsExponent v` composed with
  `ideleCoordinate v` (modules `LocalUnitCohomology` and `IdeleCohomology` of
  `Langlands.ClassField.Global`). As an integer it is the negative of the Library's
  `ideleOrder v`, so a uniformizer has exponent `-1`.
- `ideleExponent_eq_one_iff`: the exponent is trivial iff the `v`-coordinate has valuation `1`.
- `exp_ideleExponent_unitEmbedding`: for `a ∈ Kˣ`, `exp` of the exponent of the principal idele
  of `a` is the `v`-adic valuation `v.valuation K a`. `ideleExponent_unitEmbedding_eq_one_iff`
  is the corresponding statement for exponent `1`.
- `sUnitIdeles K S` is the subgroup `⨅ v ∉ S, ker (ideleExponent v)`: the ideles that are
  valuation units at every finite place outside `S`. No condition is imposed at the places of
  `S` or at the infinite places. `mem_sUnitIdeles_iff` unfolds membership, and
  `sUnitIdeles_mono` shows that the group grows with `S`.
- `unitEmbedding_mem_sUnitIdeles_iff`: the principal idele of `a ∈ Kˣ` lies in `sUnitIdeles K S`
  iff `a` is an `S`-unit, i.e. `a ∈ sUnits K S`, the Mathlib group `(↑S).unit K` named in the
  Library module `Langlands.Global.Arithmetic.SUnitIndex`.
- `unitEmbedding_injective`: `Kˣ → J_K` is injective, since `K` embeds in its adele ring
  (Mathlib's `AdeleRing.algebraMap_injective`).
- `sUnitsToIdeles K S : sUnits K S →* sUnitIdeles K S` is the principal-idele map restricted to
  `S`-units. `sUnitsToIdeles_injective` shows it is injective. `range_sUnitsToIdeles` shows that
  its image is exactly the group of principal ideles in `sUnitIdeles K S`, i.e.
  `(principalSubgroup).subgroupOf (sUnitIdeles K S)`.

## Generation by principal ideles

- `HasGlobalUniformizers K S` is the following condition. Every finite place `v ∉ S` has an
  element `π ∈ Kˣ` whose principal idele has exponent `-1` at `v` and exponent `1` (valuation
  one) at every finite place `w ∉ S` with `w ≠ v`. `HasGlobalUniformizers.mono` shows that the
  condition is preserved under enlarging `S`. The condition says that the classes of the
  places of `S` generate the ideal class group, but the module never uses that reformulation.
- `exp_ideleExponent_algebraMap`: for a nonzero algebraic integer `r`, `exp` of the exponent
  of its principal idele is the integral valuation `v.intValuation r`.
- `exists_hasGlobalUniformizers K S₀`: every finite set `S₀` is contained in a finite set `S`
  with global uniformizers. Proof: for each ideal class `c`, choose a nonzero integral ideal
  `I_c` in `c` (Mathlib's `ClassGroup.mk0_surjective`; the class group is finite). Let `S` be
  `S₀` together with all places dividing some `I_c`; this set is finite by
  `Ideal.finite_factors`. For `v ∉ S`, take `c = [v]⁻¹`. Then `v · I_c` is principal
  (`ClassGroup.mk0_eq_one_iff`), say `v · I_c = (π)`.
  - The `v`-adic valuation of `π` is exactly `exp (-1)`: `v ∣ (π)`, while `v² ∣ v · I_c` would
    give `v ∣ I_c`, i.e. `v ∈ S` (Mathlib's `intValuation_le_pow_iff_dvd`).
  - For `w ∉ S`, `w ≠ v`: if `π ∈ w`, then `v · I_c ⊆ w`, so `v ⊆ w` (hence `v = w` by
    maximality) or `I_c ⊆ w` (hence `w ∈ S`). So `π ∉ w` and its valuation at `w` is `1`.
- `principal_sup_sUnitIdeles`: if `S` has global uniformizers, then
  `principalSubgroup ⊔ sUnitIdeles K S = ⊤`, i.e. `J_K = K^× · J^S`. Proof: an idele `y` has
  nonzero exponent at only finitely many finite places (the Library's
  `ideleOrder_finite_support`). Let `T` be this finite set, and for `v ∈ T ∖ S` let `n_v` be the
  exponent of `y` at `v`. Put `a = ∏_{v ∈ T ∖ S} π_v ^ {n_v}`. Then `y · a` has exponent `0` at
  every finite `w ∉ S`. At `w ∈ T` the factor `π_w ^ {n_w}` contributes `-n_w`, and all the other
  factors are units there. At `w ∉ T`, all the factors are units. Hence
  `y = a⁻¹ · (y · a) ∈ K^× · J^S`. In Lean, `π_v` is taken to be `1` for `v ∈ S`, and the
  product runs over all of `T`.

## Provenance

The statement `J_k = k^× J_k^{S}` for `S` large is used by Artin–Tate, *Class Field Theory*,
Chapter VI §3, in the proof of Lemma 3 (printed p. 26), where it is attributed to the finiteness
of the class group. The precise condition `HasGlobalUniformizers` and the Lean proofs are
internal. They use only Mathlib's ideal factorization and class group, and not the Library's
`PrincipalIdeleDivisorFormula` statement.
