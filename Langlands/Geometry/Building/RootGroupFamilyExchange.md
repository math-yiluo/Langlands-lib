# Exchange of opposite products for a family of root subgroups

Module `Langlands.Geometry.Building.RootGroupFamilyExchange`. Internal unit.
It repeats the argument of the published `ChamberExchange` module for an
arbitrary family of subgroups `U : characterLattice S → Subgroup G(k)` in
place of the zero-depth filtration groups `b ↦ U_{b,x,0}` at one point.

## Declarations (namespace `Langlands.Geometry.Building.RootGroupFamily`)

- `span U P = ⨆ b ∈ P, U b` and `exchangeSet i U H w =
  span U Φ_{-w} * span U Φ_w * H` for a subgroup `H` and a real vector `w`,
  with `Φ_w = realPositiveRoots i w`.
- `HasCommutatorRelations i U`: for relative roots `c, b` with
  `1 ⊗ b ≠ -(t • 1 ⊗ c)` for all `t > 0`,
  `⁅U c, U b⁆ ≤ ⨆_{p,q > 0, p c + q b ∈ Φ} U (p c + q b)` (the shape of V 3 in
  the published `filtration_commutator_le`).
- `HasRayProperty i`: relative roots `c, d` with `eval d = t • eval c`,
  `t > 0`, satisfy `d = c ∨ d = 2c ∨ c = 2d`.
- `le_normalizer_span`, `span_le_normalizer_span`, `span_cross_mul_subset`,
  `exchangeSet_subset`, `exchangeSet_eq`, `exchangeSet_tmul_eq_neg`,
  `mul_mem_exchangeSet`: the steps of `ChamberExchange` (`rootSpan_…`,
  `exchangeSet_…`) with `D.filtration x b 0` replaced by `U b`,
  `filtration_double_le` replaced by the hypothesis `U (2c) ≤ U c`, and
  `eq_or_double_of_eval_eq_smul` replaced by `HasRayProperty`.
- `iSup_subset_mul_of_exchange`: if `U` has the commutator relations,
  `Φ` is finite and closed under negation, `HasRayProperty i` holds,
  `U (2c) ≤ U c` whenever `c, 2c ∈ Φ`, and the rank-one exchanges
  `U (-c) * U c ⊆ U c * U (-c) * H` hold for all `c ∈ Φ`, then for every
  generic cocharacter `mu`,

  `(⨆ α ∈ Φ, U α) ⊆ (⨆ b ∈ Φ_{-mu}, U b) * (⨆ b ∈ Φ_mu, U b) * H`.

  The proof moves a real vector from `mu` to `-mu`, crossing one ray of roots
  at a time, exactly as in `KPApartmentData.sharpFixer_subset_mul_of_exchange`.

## Provenance

Internal generalization of the published `ChamberExchange` argument (the
range part of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, 2023,
Proposition 7.3.12(1)). The public helper lemmas of `ChamberExchange`
(`le_normalizer_iSup_of_commutator_le`, `eq_of_forall_single_crossing`,
`combination_pos_of_crossing`, `tmul_ne_neg_smul_of_crossing`,
`mem_Ioo_of_mul_neg`, `isRayCrossing_of_forall_pos`) are reused unchanged.
