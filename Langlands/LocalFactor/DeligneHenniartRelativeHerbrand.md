# Relative Herbrand functions between intermediate fields

Lean module: `Langlands.LocalFactor.DeligneHenniartRelativeHerbrand`.

## Source

P. Deligne and G. Henniart, *Sur la variation, par torsion, des constantes locales
d'équations fonctionnelles de fonctions L*, Invent. Math. 64 (1981):

- 3.1–3.2 (printed pp. 102–103, PDF pp. 14–15). For finite separable `K ⊆ L ⊆ M`, DH81
  set `ψ_{M/L} = ψ_M ∘ ψ_L⁻¹`. Proposition 3.2(iii) says: once the upper group lies in
  `Gal(N/M)` (the index is "grand"), the slope of `ψ_{M/L}` is the ramification index
  `e(M/L)`. The proof computes the slope as the index `[G[0] : H[0]]` of (3.2.1).
- 3.12(i) (printed p. 107, PDF p. 19), the first-order norm–trace congruence. It enters
  only as the hypothesis `TopLayerNormTraceStatement` of the Library module
  `DeligneHenniartTopLayerStatement`.
- 4.3–4.4 and 4.7 (printed pp. 109–110, PDF pp. 21–22), which use these Herbrand facts for the fields
  `E ≤ L` of an induction.

The Library states the inputs of the witness lemmas 4.3 and 4.7 as the propositions
`ApproximateHerbrandInput F E L h U b` (module `DeligneHenniartApproximateDimensionOne`)
and `HerbrandInputRel F E L h b` (module `DeligneHenniartDimensionOneRelative`). This module
proves them for `U = intermediateUpperGroup F E`. The construction (composite at finite
level in a Galois closure over `F`) is derived for this formalization. The mathematics is
DH81 3.1–3.2 and Herbrand's theorem.

## Generic tower section (namespace `Langlands.Ramification.HerbrandBridge`)

Setting: `p`-adic fields `F, K, E` with algebras `K → E`, `F → K`, `F → E` and maps of
`K` and `E` into `Ω = AlgebraicClosure F` forming scalar towers. `M` is a finite Galois
subfield of `Ω` over `F`, and `hE` says that the image of `E` lies in `M`. Write `P` for `M`
viewed over `E` (`finiteGaloisPadicField E (extendFiniteGalois hE)`), with its canonical
topological data. `relativeIndex F M h u` is the Library's `φ_{M/K} ∘ ψ_{M/F}`.

Definitions:

- `towerIndex F K hE v := φ_{P/E}(ψ_{P/K}(v))`. This is `ψ_{E/K}` computed in `P`.
- `towerRatio F K hE : ℕ`: the relative index of the image of `Gal(P/E)` in the lower
  group `G_0` of `Gal(P/K)`. This is `[G_0 : G_0 ∩ Gal(P/E)]`.
- `towerFieldEquiv`: the identity of `M` as a `K`-algebra isomorphism between `M` viewed
  over `K` and `M` viewed over `E`.

Theorems:

- `algebraMap_mem_of_tower`: the image of `K` lies in `M`.
- `towerField_isScalarTower`: the scalar tower `F → K → P` (local instance).
- `relativeIndex_eq_tower`: `ψ_{K/F}(u)` computed in `M` over `K` equals
  `φ_{P/K}(ψ_{P/F}(u))` computed in `P`.
- `towerIndex_relativeIndex` (transitivity): `ψ_{E/K}(ψ_{K/F}(u)) = ψ_{E/F}(u)`, where both
  `ψ_{·/F}` are `relativeIndex F M`.
- `towerIndex_zero`, `towerIndex_continuous`, `towerIndex_strictMono`.
- `towerIndex_le_mul`: `ψ_{E/K}(s) ≤ towerRatio · s` for `s ≥ 0`.
- `absoluteRelativeRestriction_apply_coe`: the restriction to `M` of `τ ∈ Gal(Ω/F)`,
  read in `Ω`, is `τ`.
- `absoluteRelativeRestriction_mem_range_iff`: the restriction of `τ` lies in the image
  of `Gal(P/K)` exactly when `τ` fixes the image of `K`.
- `upperRamificationGroup_le_range_of_fix` (with `u₀ ≥ -1`). Hypothesis: every `τ` in
  `absoluteUpperRamificationGroup F u₀` that fixes `K` also fixes `E`. Conclusion: the
  upper group of `Gal(P/K)` of index `ψ_{K/F}(u₀)` lies in the image of `Gal(P/E)`.
- `towerIndex_sub_eq` (DH81 3.2(iii)). Same hypothesis, with `u₀ ≥ 0`. For
  `ψ_{K/F}(u₀) ≤ s ≤ t`: `ψ_{E/K}(t) − ψ_{E/K}(s) = towerRatio · (t − s)`.
- `towerRatio_mul_relIndex`. Let `SK`, `SE` be subgroups of `Gal(Ω/F)` characterized as
  the fixers of `K` and `E`. Then
  `towerRatio · [I_F : I_F ∩ SK] = [I_F : I_F ∩ SE]`, where
  `I_F = F.absoluteInertia F.canonicalTopologicalData`.
- `topLayer_of_fix` (DH81 3.12(i) along the tower). Inputs:
  - `htop : TopLayerNormTraceStatement`;
  - an integer `n ≥ 1` and `u₀ ≥ -1` with `ψ_{K/F}(u₀) = n`;
  - the fixing hypothesis above.

  Conclusion: for nonzero `y ∈ E` with `ψ_{E/K}(n) ≤ ord_E y`, `Tr_{E/K} y` lies in
  `additiveLattice (−n)` of `K`. Moreover, for units `z = 1 + y` of `E` and
  `t = 1 + Tr_{E/K} y` of `K`, `N_{E/K}(z) t⁻¹ ∈ U_K^{n+1}`.
- `exists_relativeIndex_eq`: for `v ≥ 0` there is `u ≥ 0` with `ψ_{E/F}(u) = v`.

## Specialization to `E ≤ L` (namespace `Langlands.LocalFactor.NonabelianSystem.DeligneHenniart`)

`E, L : Extension F` are finite intermediate fields of `AlgebraicClosure F` with
`h : E.field ≤ L.field`. `relativeHerbrandPsi E` is the Library's `ψ_{E/F}`. Upper groups
of `W_E` are the carried groups `intermediateUpperGroup F E s`. `e_E` is
`(fieldData F E).ramificationIndex`; the Library's `fieldData_ramificationIndex_eq` gives
`e_E = [I_F : I_F ∩ G_E] · e_F`.

Definition:

- `intermediateHerbrandPsi F E L h`. This is `towerIndex` for
  `K = E.asPadicField`, the larger field `L.asPadicField`, and `M = galoisClosure L`, with
  the algebra `E → L` given by `IntermediateField.inclusion h`. So
  `ψ_{L/E} = φ_{M/L} ∘ ψ_{M/E}`.

Theorems:

- `exists_relativeHerbrandPsi_eq`: `ψ_{E/F}` takes every value `v ≥ 0` at some `u ≥ 0`.
- `intermediateUpperGroup_eq_weilUpperSubgroup`:
  `intermediateUpperGroup F E s = weilUpperSubgroup F E s`.
- `intermediateHerbrandPsi_zero`, `_continuous`, `_strictMono`.
- `galoisClosure_le`: `galoisClosure E ≤ galoisClosure L`.
- `intermediateHerbrandPsi_relativeHerbrandPsi`:
  `ψ_{L/E}(ψ_{E/F}(u)) = ψ_{L/F}(u)`.
- `weilInclusion_mem_intermediateUpperGroup_iff` (Herbrand's formula). For `v ≥ 0` and
  `g ∈ W_L`: `g ∈ W_E^v` (through `weilInclusion F E L h`) iff `g ∈ W_L^{ψ_{L/E}(v)}`.
- `fix_of_intermediateUpperGroup_le`. Hypotheses: `u₀ ≥ 0` and
  `W_E^{ψ_{E/F}(u₀)} ⊆ W_L`. Conclusion: every `τ ∈ G_F^{u₀}` that fixes `E` fixes `L`.
- `towerRatio_mul_ramificationIndex`: `towerRatio · e_E = e_L`.
- `ramificationIndex_mul_intermediateHerbrandPsi_sub` (DH81 3.2(iii)). If `u₀ ≥ 0` and
  `W_E^{ψ_{E/F}(u₀)} ⊆ W_L`, then for `ψ_{E/F}(u₀) ≤ s ≤ t`:
  `e_E (ψ_{L/E}(t) − ψ_{L/E}(s)) = e_L (t − s)`.
- `ramificationIndex_mul_intermediateHerbrandPsi_le`: `e_E ψ_{L/E}(s) ≤ e_L s` for
  `s ≥ 0`.
- `herbrandInputRel_of_le`: if `W_E^{b/2} ⊆ W_L` then `HerbrandInputRel F E L h b`.
- `approximateHerbrandInput_of_le`. Hypotheses: `htop : TopLayerNormTraceStatement`
  (all universes `uF`), `b ≥ 1`, and `W_E^b ⊆ W_L`. Conclusion:
  `ApproximateHerbrandInput F E L h (intermediateUpperGroup F E) b`.

## Proof (as implemented)

- **Transport.** `relativeIndex_eq_tower` rewrites the Herbrand functions of `M` over `K`
  as those of `P`, using `herbrandPsi_eq_of_algEquiv` and `herbrandPhi_eq_of_algEquiv`
  along `extendFiniteGaloisEquiv` and `towerFieldEquiv`. Transitivity then is
  `herbrandPsi_herbrandPhi` in `P`.
- **Fixing condition to finite level.** Take `σ` in the upper group of `Gal(P/K)` of index
  `ψ_{K/F}(u₀)`. Herbrand's formula `restrictScalars_mem_upperRamificationGroup_iff` puts
  `σ` over `F` in the upper group of `Gal(P/F)` of index `u₀`. This is the image of
  `G_F^{u₀}` (`map_absoluteRelativeRestriction_upper`), so `σ` lifts to some
  `τ ∈ G_F^{u₀}`. `τ` fixes `K` by `absoluteRelativeRestriction_mem_range_iff`, hence
  fixes `E` by hypothesis. Then `mem_comap_absoluteRelativeRestriction_iff` gives
  `σ ∈ Gal(P/E)`.
- **Slope and bound.** The slope is the Library's `herbrandPhi_herbrandPsi_sub_eq` with
  `K, E, P` and `v₀ = ψ_{K/F}(u₀) ≥ 0`. The bound is `herbrandPhi_herbrandPsi_le_mul`.
- **Ratio.** In `P`, `lowerGroupOrder_subfield_mul_relIndex` for the three pairs
  `(F, E)`, `(F, K)`, `(K, E)` gives
  `|G_0(P/E)| · [ratio for K ⊆ E] · [ratio for F ⊆ K] = |G_0(P/E)| · [ratio for F ⊆ E]`.
  `G_0(P/F)` is the image of `I_F` (`absoluteUpperCanonicalInertia`,
  `map_absoluteRelativeRestriction_upper` at `0`), so the indices over `F` are absolute
  inertia indices (`relativeSubgroup_relIndex_eq`, `Subgroup.relIndex_comap`). Cancel the
  positive order `lowerGroupOrder_pos`. For `E ≤ L` this is combined with
  `fieldData_ramificationIndex_eq` (`e_E = [I_F : I_F ∩ G_E] · e_F`).
- **Top layer.** `topLayer_of_fix` applies `htop` to `K ⊆ E ⊆ P`. It builds the scalar
  towers, finiteness and `IsGalois K P` (`IsGalois.tower_top_of_isGalois`). The threshold
  `w < n` comes from `exists_lt_upperRamificationGroup_eq`: the upper group at some
  `w < n` equals the one at `n`. That group lies in `Gal(P/E)` by the fixing step.
- **Specialization.** The algebra `E → L` and the scalar tower into `Ω` are local
  `letI`s. `relativeIndex_eq_of_le` with `galoisClosure_le` replaces `ψ_{E/F}` computed in
  `galoisClosure L` by `relativeHerbrandPsi E`. For Herbrand's formula, write
  `v = ψ_{E/F}(u)` with `u ≥ 0` and apply the base comparison `coe_mem_upperGroup_iff` at
  `E` and at `L`, together with transitivity. For the fixing lemma, transport `τ`
  (which lies in inertia) to the Weil group with `localInertiaEquiv`. Its image lies in
  `W_E^{ψ_{E/F}(u₀)}` by `coe_mem_upperGroup_iff`, hence in `W_L`, so `τ` fixes `L`.
- **Inputs.** `herbrandInputRel_of_le` takes `u₀` with `ψ_{E/F}(u₀) = b/2` and uses the slope
  on `[b/2, b]`. `approximateHerbrandInput_of_le` takes `u₀` with `ψ_{E/F}(u₀) = b` and
  applies `topLayer_of_fix` with `n = b`.
