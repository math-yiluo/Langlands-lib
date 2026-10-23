# Averaging against smooth functionals, and compact open bases of product Levis

Author: Worker 252.

This helper module supports the forward direction (quasicuspidal ⇒ compact
coefficients) of `Langlands.CuspidalSupport.LeviHarishChandraTheorem`. It is
internal infrastructure, not a result quoted from the literature. The averaging
identity is the standard fact used throughout Bernstein–Zelevinsky (1976), §2,
that averaging over a compact open subgroup `K` is the identity on `K`-fixed
vectors, here read on the dual side.

## Averaging and smooth functionals

Fix a topological group `G` and a complex representation `ρ` on `V` that is
smooth (`Langlands.IsSmooth ρ`). All declarations below live in the
`Langlands` namespace, which is omitted from their names.

- `Compact.dual_averageMap_eq_of_mem_fixedVectors`: let `K` be a compact open
  subgroup and `ℓ : Module.Dual ℂ V` be fixed by `K` under `ρ.dual`. Then
  `ℓ (averageMap ρ hρ K hK w) = ℓ w` for every `w`.

  *Proof.* `averageMap` is the orbit mean of `w` under `ρ` restricted to `K`.
  `Compact.orbitMean_eq_finiteMean` writes it as the uniform average of the
  finite orbit. Each orbit point is `ρ k w`, and `ℓ (ρ k w) = ℓ w` because `ℓ`
  is fixed by `k⁻¹` under the dual action. So `ℓ` takes the value `ℓ w` at every
  orbit point, and the uniform average of a constant is that constant.

- `Compact.exists_dual_averageMap_eq`: assume that compact open subgroups form a
  neighbourhood basis of `1` in `G`, stated as the hypothesis `hbasis`. Let `ℓ`
  be a smooth vector of `ρ.dual` (`IsSmoothVector ρ.dual ℓ`). Then, for every
  neighbourhood `U` of `1`, there is a compact open subgroup `K ⊆ U` with
  `ℓ (averageMap ρ hρ K hK w) = ℓ w` for every `w`.

  *Proof.* Smoothness gives an open subgroup `H` fixing `ℓ`. Apply `hbasis` to
  `U ∩ H` to get a compact open `K ⊆ U ∩ H`. Then `K` fixes `ℓ`, and the
  previous lemma applies.

The basis hypothesis is explicit because the pinned Mathlib has no general van
Dantzig theorem for totally disconnected locally compact groups. The two
groups this task needs are covered by the next section.

## Compact open bases of product Levis and of `G°`

Fix `p`, `F : PadicField.{uF} p`, `T : F.TopologicalData`, `n` and
`B : BlockShape n`. Write `G = B.Levi F.Carrier`, the product over the blocks
`j` of `GeneralLinear (B.size j) F.Carrier`, with the product topology from
`T.topology`.

- `CuspidalSupport.leviPiOpenSubgroup T B K`: for a family `K j` of open
  subgroups of the factors, the product subgroup `Subgroup.pi Set.univ K`
  as an open subgroup of `G`. It is open because a finite product of open sets
  is open in the product topology.
- `CuspidalSupport.mem_leviPiOpenSubgroup`: `g` lies in it iff `g j ∈ K j` for
  every `j`.
- `CuspidalSupport.isCompact_leviPiOpenSubgroup`: it is compact when every
  `K j` is compact (Tychonoff for a product of compact sets).
- `CuspidalSupport.exists_leviPiOpenSubgroup_subset S`: for a refinement
  `S : BlockRefinement B` and every neighbourhood `U` of `1` in `G`, there is a
  family `K` of compact open subgroups of the factors such that each `K j` has a
  block Iwahori factorization for `S j` and the product lies in `U`.

  *Proof.* A neighbourhood of `1` in the finite product contains a product of
  factor neighbourhoods `O j` (`nhds_pi`, `Filter.mem_pi'`). The published
  `BlockRefinement.blockIwahoriBasis` gives, in each factor, a compact open
  subgroup `K j ⊆ O j` with the block Iwahori factorization for `S j`.
- `CuspidalSupport.levi_exists_compact_openSubgroup_subset`: compact open
  subgroups form a neighbourhood basis of `1` in `G`. This applies the previous
  lemma to the refinement with one block in each factor.
- `CuspidalSupport.determinantUnit_exists_compact_openSubgroup_subset`: compact
  open subgroups form a neighbourhood basis of `1` in
  `G° = determinantUnitSubgroup T B`, with the subspace topology.

  *Proof.* A neighbourhood of `1` in `G°` is the trace of a neighbourhood `u` of
  `1` in `G` (`mem_nhds_subtype`). Take a compact open `N ⊆ u` in `G`. Its
  preimage under the continuous inclusion is an open subgroup of `G°` inside
  the given neighbourhood. `G°` is an open, hence closed, subgroup of `G`, so
  the inclusion is a closed embedding and the preimage of the compact set `N`
  is compact.

So `Compact.exists_dual_averageMap_eq` applies to `G°` with
`hbasis := determinantUnit_exists_compact_openSubgroup_subset T B`.
