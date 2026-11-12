# Level claims for norm images of unit filtrations, and their tower law

Helper module for the proof of
`Langlands.LocalClassField.FiniteAbelianNormUnitImageCardinality`. The
definition `LevelClaims` is internal to this proof: it is not a statement from
the literature. It records, in divisibility form, the bounds that Serre,
*Local Fields*, Chapter XV, §2 (with the norm computations of Chapter V, §6)
uses to identify the image of a unit level in the norm quotient.

## The definition `LevelClaims K L`

Let `K` and `L` be p-adic fields with a finite extension `L/K` compatible with
`ℚ_p`, both equipped with their canonical topological data (canonical valuation,
unit filtration `U^n`, and upper ramification groups). For a real number `a ≥ 0`
write

- `n = ⌈a⌉₊`,
- `m = ⌈ψ_{L/K}(a)⌉₊`, where `ψ_{L/K}` is the Herbrand function
  `Padic.herbrandPsi`,
- `G^a` for the upper ramification group of `L/K` at `a`,
- `N` for the unit norm `normUnits K L : Lˣ →* Kˣ`, and `N(Lˣ)` for the norm
  subgroup `normSubgroup K L`.

`LevelClaims K L` states that for every `a ≥ 0`:

1. (C) `N(U_L^m) ≤ U_K^n`;
2. (V) the relative index of `N(U_L^m)` in `U_K^n` divides `|G^a|`;
3. (WZ) `[Kˣ : U_K^n · N(Lˣ)] · |G^a|` divides `[L : K]`.

Here `|·|` is `Nat.card` and indices are `Subgroup.index` and
`Subgroup.relIndex`, which take the value `0` for infinite indices. No
finiteness side condition is part of the definition.

## Lemmas

- `normUnits_comp`: for a tower `K ⊆ E ⊆ L`, the unit norm of `E/K` composed
  with that of `L/E` is the unit norm of `L/K`. This is the transitivity of the
  norm, `Algebra.norm_norm`.
- `normSubgroup_map_tower`: the norm of `E/K` maps `N_{L/E}(Lˣ)` onto
  `N_{L/K}(Lˣ)`. It follows from `normUnits_comp` and `MonoidHom.map_range`.
- `card_upperRamificationGroup_tower`: for Galois extensions `L/K`, `E/K`,
  `L/E` and `a ≥ 0`,
  `|G(L/K)^a| = |G(E/K)^a| · |G(L/E)^{ψ_{E/K}(a)}|`.
  The proof splits `G(L/K)^a` along the restriction homomorphism
  `Gal(L/K) → Gal(E/K)` with `card_eq_card_map_mul_card_inf_ker`. The image of
  `G(L/K)^a` is `G(E/K)^a` by Herbrand's theorem, in the form
  `HerbrandBridge.upperRestrictionCompatibility`. The intersection of the
  kernel with `G(L/K)^a` is the image of `G(L/E)^{ψ_{E/K}(a)}` under
  `AlgEquiv.restrictScalarsHom`. This uses the transitivity
  `ψ_{L/K} = ψ_{L/E} ∘ ψ_{E/K}` (`HerbrandBridge.herbrandPsi_tower`) and the
  description of the upper groups of the subgroup `Gal(L/E)`
  (`HerbrandBridge.restrictScalars_mem_upperRamificationGroup_iff`,
  `HerbrandBridge.towerSubgroupEquiv`). The map `restrictScalarsHom` is
  injective, so this image has the same order as `G(L/E)^{ψ_{E/K}(a)}`.

## The tower law `levelClaims_tower`

If `K ⊆ E ⊆ L` with `L/K`, `E/K`, `L/E` Galois, then `LevelClaims K E` and
`LevelClaims E L` imply `LevelClaims K L`.

Fix `a ≥ 0` and put `b = ψ_{E/K}(a) ≥ 0`, `n = ⌈a⌉₊`, `k = ⌈b⌉₊` and
`m = ⌈ψ_{L/E}(b)⌉₊`. Because `ψ_{L/K}(a) = ψ_{L/E}(b)`, `m` is also the
level used for `L/K` at `a`. Apply the claims for `E/K` at `a` and for `L/E` at
`b`, and rewrite `|G(L/K)^a|` with `card_upperRamificationGroup_tower`.

- (C) By transitivity of the norm,
  `N_{L/K}(U_L^m) = N_{E/K}(N_{L/E}(U_L^m)) ≤ N_{E/K}(U_E^k) ≤ U_K^n`.
- (V) The relative index of `N_{L/K}(U_L^m)` in `U_K^n` is the product of its
  relative index in `N_{E/K}(U_E^k)` and the relative index of
  `N_{E/K}(U_E^k)` in `U_K^n` (`Subgroup.relIndex_mul_relIndex`). The second
  factor divides `|G(E/K)^a|`. The first factor divides the relative index of
  `N_{L/E}(U_L^m)` in `U_E^k` (`relIndex_map_dvd`), which divides
  `|G(L/E)^b|`.
- (WZ) Put `A = U_K^n · N_{L/K}(Lˣ)` and `B = U_K^n · N_{E/K}(Eˣ)`, so
  `A ≤ B` and `[Kˣ : A] = [B : A] · [Kˣ : B]`. Using (C) for `E/K` and
  `normSubgroup_map_tower`, `A = U_K^n · N_{E/K}(U_E^k · N_{L/E}(Lˣ))` and
  `B = U_K^n · N_{E/K}(Eˣ)`. Hence `relIndex_sup_map_dvd` shows that `[B : A]`
  divides `[Eˣ : U_E^k · N_{L/E}(Lˣ)]`. Multiplying the (WZ) divisibilities for
  `E/K` and `L/E` and using `[L : K] = [L : E] · [E : K]` gives
  `[Kˣ : A] · |G(L/K)^a| ∣ [L : K]`.
