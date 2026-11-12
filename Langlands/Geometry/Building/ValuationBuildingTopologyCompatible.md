# Axiom V 7 for every building datum

Module `Langlands.Geometry.Building.ValuationBuildingTopologyCompatible`.

This module proves KP axiom V 7 (Kaletha–Prasad, *Bruhat–Tits theory: a new approach*,
Definition 6.1.2, V 7, printed p.199 / PDF p.230) for every `B : ValuationBuildingData G` over
a nonarchimedean local field `F`, in either characteristic. It adds no hypothesis to the
published data.

## The proposition

`ValuationBuildingTopologyCompatibleStatement.{u} : Prop` says: for every nonarchimedean local
field `F : Type u`, every group scheme `G` over `Spec F` with `[IsAffineHom G.X.hom]`, and every
`B : ValuationBuildingData G`, `B.IsTopologyCompatible` holds.

`B.IsTopologyCompatible` is the published `B.apartment.IsTopologyCompatible`. The topology on
`G(F)` is the published `rationalPointTopology F G.X`. For every valuation `x` of the class
`A(S)` of `B` and every relative root `a`:

- the sets `U_{a,x,r} = {u ∈ U_a(F) | x_a(u) ≥ r}` (`r ∈ ℝ`) are open in `U_a(F)`;
- each is algebraically bounded in `G(F)` (KP Definition 2.2.1, printed p.70 / PDF p.101);
- they form a neighbourhood base of `1` in `U_a(F)`.

The module proves it in two forms:

- `ValuationBuildingData.isTopologyCompatible (B) : B.IsTopologyCompatible`;
- `valuationBuildingTopologyCompatible : ValuationBuildingTopologyCompatibleStatement.{u}`.

### Provenance

The proposition is derived, not quoted. It is the V 7 conjunct of the published target
`ValuationBuildingApartmentAxiomsStatement` (see
`ValuationBuildingData.satisfiesApartmentAxioms_iff`), split off as an intermediate result
toward that target. It contains no other apartment axiom.

KP impose V 7 as an axiom in Definition 6.1.2. For the class of Theorem 9.6.5, V 7 holds
because that class comes from the Bruhat–Tits construction (§9.5–9.6, printed pp.363–367 /
PDF pp.394–398). Every `ValuationBuildingData` class equals that class by KP Proposition 6.2.6
(printed p.216 / PDF p.247). The proposition asks for V 7 for every class directly. It adds no
quasi-splitness, residue-field, tameness or simply-connectedness condition, and no apartment
axiom.

The proof below derives V 7 from V 0, V 1, V 6 and the group structure. It does not follow
KP's route through Proposition 6.2.6 and descent.

## Proof

The proof has three parts.

### 1. An abstract criterion (`contracting_*`)

Let `U` be a topological group and `f : U → ℝ ∪ {∞}` a function with these properties:

- `f⁻¹(∞) = {1}`, and every superlevel set `filt r = {f ≥ r}` is a subgroup;
- `f` is locally constant on `U ∖ {1}`;
- an automorphism `σ` of `U` (a `ContinuousMulEquiv`) satisfies `f ∘ σ = f + c` with
  `c > 0`, and `σⁿ(g) → 1` for every `g`;
- `U` has a compact open identity neighbourhood `K` and a point `≠ 1`.

Then every `filt r` is open and compact, and the `filt r` form a neighbourhood base of `1`.
The proof goes as follows.

- `contracting_iterate_shift`: `f(σⁿ g) = f(g) + n c`.
- `contracting_exists_mem_ne_one`: `filt r` contains a point `g ≠ 1`, namely `σⁿ g₀` for
  large `n`.
- `contracting_isOpen`: by local constancy `filt r` is a neighbourhood of that `g`, so the
  subgroup `filt r` is open (`Subgroup.isOpen_of_mem_nhds`).
- `contracting_exists_bound`: `A = K ∖ σ(K)` is compact (`σ(K)` is open) and avoids `1`,
  so the locally constant `f` is bounded on `A` by some `M`. If `u ∉ K`, let `n ≥ 1` be the first index with `σⁿ u ∈ K`. Then `σⁿ u ∈ A`, so
  `f(u) = f(σⁿ u) - n c ≤ M`. Hence `{f > M} ⊆ K`.
- `contracting_isCompact`: for `n` with `r + n c > M`, `filt r ⊆ σ⁻ⁿ(K)`, which is compact.
  An open subgroup is closed, so `filt r` is compact.
- `contracting_hasBasis`: the `filt n` (`n ∈ ℕ`) are decreasing, compact, and their
  intersection is `f⁻¹(∞) = {1}`. Mathlib's `exists_subset_nhds_of_isCompact` then puts one of
  them inside any neighbourhood of `1`.

### 2. Local constancy of the root values (`eventually_val_eq`)

Let `u ∈ U_a(F) ∖ {1}`. Then every `v ∈ U_a(F) ∖ {1}` close enough to `u` satisfies
`x_a(v) = x_a(u)` at every apartment point `x`.

- `exists_isOpen_centralizer_normKernel`: there is an open `W ∋ 1` in `G(F)` whose points in
  `Z(F)` lie in `Z(F)^1`. It comes from `isOpen_rationalCommonNormKernel` for `Z` and the
  embedding `isEmbedding_rationalPointMap` of the closed immersion `Z → G`.
- Choose `ν` with `⟨a, ν⟩ > 0` (`IsSplitTorus.exists_pairing_eq_pos`) and let
  `χ = (-ν) ∘ i`. By `RelativeRoot.subgroup_le_dynamicUnipotent` and
  `groupHom_neg_comp_eq_oppositeCocharacter`, `U_a(F) ⊆ U(χ⁻¹)(F)` and
  `U_{-a}(F) ⊆ U(χ)(F)`. By `torusCentralizer_le_dynamicCentralizer`, `Z(F) ⊆ Z(χ)(F)`.
- Take opposite factor pairs `p` of `u` and `q` of `v`
  (`exists_isOppositeFactorPair` with `rootRankOneFactorization`), and let
  `n = m(u) = p₁ u p₂`. The continuous map `w(v) = n⁻¹ p₁ v p₂` has `w(u) = 1`. It factors as
  `w(v) = (n⁻¹ p₁ q₁⁻¹ n) · (n⁻¹ m(v)) · (q₂⁻¹ p₂)`. The first factor lies in `U_a(F)`
  (`IsOppositeFactorPair.inv_conj_mem`). The second lies in `Z(F)`
  (`reflectionElement_inv_mul_mem_centralizer`). The third lies in `U_{-a}(F)`.
- By `Dynamic.opposite_cell_mem_nhds_one`, the products `o · z · c` with middle factor in `W`
  form a neighbourhood of `1`. For `v` near `u`, `w(v)` lies in it.
  `dynamic_opposite_factorization_unique` then gives `n⁻¹ m(v) ∈ W ∩ Z(F)`, so
  `n⁻¹ m(v) = j(z)` with `z ∈ Z(F)^1`.
- `z` fixes the apartment (`IsOmegaCompatible.smul_eq_self`), so `m(v) · x = m(u) · x`.
  `m(u)` acts as the reflection `y ↦ y - ψ^u_a(y) · ǎ_u`
  (`normalizerAffineEquiv_reflectionElement`), and `a(ǎ_u) = 2`
  (`rootForm_reflectionCoroot`). Applying `a` to `m · x - x` gives `ψ^v_a(x) = ψ^u_a(x)`.
  Then `coe_reflectionFunctional_apply` gives `x_a(v) = x_a(u)`.

### 3. A contracting torus point (`exists_contracting_element`)

Choose `ν` with `⟨a, ν⟩ = D > 0`. Let `t = ν(π)` be the published
`CocharacterUniformizer.latticeSection` at the order-one uniformizer, and `b = i(t)`.

- `b` centralizes `S`. Conjugation by `b^{±1}` preserves `U_a(F)`
  (`conj_mem_rootGroupPoints`, `weylAction_eq_one_of_mem_centralizerPoints`).
- V 6 on `S(F)` (`isSplitTorusCompatible`) and
  `BruhatTits.SpecialCompact.localFieldOrder_latticeSection` give
  `x_a(b g b⁻¹) = x_a(g) + D`.
- `b = cocharPoint (ν ∘ i) π` (`cocharPoint_comp_eq_map_cocharacterPoints`). Since
  `U_a(F) ⊆ U(ν ∘ i)(F)`, `eventually_cocharPoint_pow_conj_mem_ambient` and
  `tendsto_uniformizerUnit_pow_zero` give `bⁿ g b⁻ⁿ → 1` for every `g ∈ U_a(F)`.

### Assembly

`rootFiltration_topology` applies part 1 to `U = U_a(F)` with the subspace topology,
`f = x_a`, `filt r = U_{a,x,r}` (a subgroup by V 1), and `σ` = conjugation by `b`. The
hypotheses come from these sources:

- `f⁻¹(∞) = {1}` is V 1.
- Local constancy is part 2.
- The shift and the contraction are part 3.
- A point `≠ 1` exists by V 0 (`three_le_encard`).
- A compact open subgroup of `U_a(F)` comes from `rationalPoint_subgroup_compactOpenCofinal`,
  as `U_a(F)` is closed (`isClosed_rootGroup`).

The basis and openness are the required ones. Compactness of `U_{a,x,r}` in `G(F)` follows
because it is the image of a compact subset of `U_a(F)`.

`isTopologyCompatible` concludes as follows. `G(F)` is Hausdorff (`rationalPoint_t2Space`),
so the compact `U_{a,x,r}` is closed. Then `localFieldAffineBoundedCompactness_proof` turns
compactness into algebraic boundedness.
