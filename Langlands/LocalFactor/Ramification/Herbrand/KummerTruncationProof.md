# The truncation lemma for the relative inverse Herbrand function

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.KummerTruncationProof`
(namespace `Langlands.Ramification.Kummer`). It imports
`Langlands.LocalFactor.Ramification.Herbrand.KummerTowerStatement` (the target statement)
and `Langlands.LocalFactor.Ramification.Herbrand.SlopeProof` (the restriction from the
absolute Galois group and the group-index lemma `relIndex_sup_of_normal`).

## Main result

`herbrandPsiTruncation : HerbrandPsiTruncationStatement.{u}`, at an arbitrary universe
level `u`. For every prime `p`, every `F : PadicField.{u} p`, every
`E : FiniteIntermediateExtension F.Carrier` and every real `μ` with
`E.field.fixingSubgroup ⊔ absoluteUpperRamificationGroup F μ = ⊤`, the relative inverse
Herbrand function satisfies `relativeHerbrandPsi E x = x` for `-1 ≤ x ≤ μ`.
This is Lemma `lem:trunc` of the operator's route note
(`operator-numerical-llc-route-2026-11-16`, lines 876-889). The Lean proof follows the
route note's argument. It uses the orders of the lower groups instead of the slopes of the
piecewise linear functions.

Notation: `G_F^v = absoluteUpperRamificationGroup F v` and `G_E = E.field.fixingSubgroup`.
`M = galoisClosure E` is the Galois closure of `E`. Inside `G = Gal(M/F)`,
`H = relativeSubgroup F h` is the image of `Gal(M/E)`. `G^v` and `G_u` are the upper and
lower ramification groups of `M/F`. By definition `ψ_{E/F} = relativeHerbrandPsi E` is
`φ_{M/E} ∘ ψ_{M/F}` (`relativeIndex`).

## Steps of the Lean proof

1. **Lower orders are proportional below the generating level**
   (`lowerGroupOrder_subfield_mul_index_of_sup_eq_top`). This is stated for a finite Galois
   `L` with realization `T`, base `K`, intermediate `E`, and `H` the image of `Gal(L/E)` in
   `Gal(L/K)`. Suppose `H ⊔ G_{u₀} = ⊤` for the real lower group `G_{u₀}`
   (`lowerRamificationGroupReal T K u₀`). Then for every natural `j` with `j - 1 < u₀`,
   `|G_j ∩ H| · [G : H] = |G_j|`; in Lean this reads
   `lowerGroupOrder T E j * H.index = lowerGroupOrder T K j`. Indeed `j ≤ ⌈u₀⌉`
   (`Int.le_ceil_iff`), so `G_{u₀} = G_{⌈u₀⌉} ≤ G_j` (`lowerRamificationGroupInt_antitone`)
   and hence `H ⊔ G_j = ⊤`. The lower group `G_j` is normal, so
   `[G_j : H ∩ G_j] = [H ⊔ G_j : H] = [G : H]` (`relIndex_sup_of_normal`,
   `Subgroup.relIndex_top_right`). Then `lowerGroupOrder_subfield_mul_relIndex` gives the
   claim.
2. **The two Herbrand functions agree on `[0, u₀]`** (`herbrandPhi_eq_of_sup_eq_top`).
   On `[0, B]`, with `B` past both ramification cutoffs, each Herbrand function is a weighted
   ramp sum divided by its order at `0` (`herbrandPhi_eq_sum`). Let `0 ≤ u ≤ u₀`. The ramp
   `ramp i` vanishes at `u` unless `i < u`. In that case `(i + 1) - 1 < u₀`, so by Step 1
   the weight over `K` at `i + 1` is `[G : H]` times the weight over `E`. Hence the ramp sum
   over `K` at `u` is `[G : H]` times the one over `E`. Step 1 at `j = 0` gives the same
   factor for the orders at `0`. The factor `[G : H]` is nonzero because the order over `K`
   at `0` is positive. So `φ_{L/E}(u) = φ_{L/K}(u)`.
3. **`φ_{L/E} ∘ ψ_{L/K}` is the identity up to `v₀`**
   (`herbrandPhi_herbrandPsi_eq_self_of_sup_eq_top`). Assume `H ⊔ G^{v₀} = ⊤` and
   `x ≤ v₀`. If `x ≤ 0`, both `ψ_{L/K}` and `φ_{L/E}` fix `x` (`herbrandPsi_of_nonpos`,
   `herbrandPhi_of_nonpos`). If `x > 0`, then `G^{v₀}` is by definition the lower group
   `G_{ψ_{L/K}(v₀)}`, and `0 ≤ ψ_{L/K}(x) ≤ ψ_{L/K}(v₀)` (positivity and monotonicity of
   `ψ`). By Step 2, `φ_{L/E}(ψ_{L/K}(x)) = φ_{L/K}(ψ_{L/K}(x)) = x`.
   `relativeIndex_eq_self_of_sup_eq_top` is this step for `relativeIndex F M h`, with
   `H = relativeSubgroup F h`.
4. **Transport of the hypothesis** (`map_absoluteRelativeRestriction_top`,
   `relativeSubgroup_sup_upper_eq_top`). Here `r = absoluteRelativeRestriction F h` is the
   restriction from the absolute Galois group of `F` to `Gal(M/F)`. Its image is all of
   `Gal(M/F)`: the case `v = -1` of `map_absoluteRelativeRestriction_upper`, together with
   `absoluteUpperRamificationGroup_neg_one` and `upperRamificationGroup_neg_one`, gives
   `r(⊤) = ⊤`. Let `-1 ≤ v` and `r⁻¹(H) ⊔ G_F^v = ⊤`. Then
   `⊤ = r(r⁻¹(H) ⊔ G_F^v) = r(r⁻¹(H)) ⊔ r(G_F^v) ≤ H ⊔ G^v` (`Subgroup.map_sup`,
   `map_absoluteRelativeRestriction_upper`, `Subgroup.map_comap_le`).
5. **The finite subextension** (`relativeHerbrandPsi_eq_self_of_sup_eq_top`). For
   `M = galoisClosure E`, the preimage of `H` is `G_E`
   (`comap_absoluteRelativeRestriction_galoisClosure`). So the hypothesis
   `G_E ⊔ G_F^μ = ⊤` with `-1 ≤ μ` gives `H ⊔ G^μ = ⊤` by Step 4. Step 3 then gives
   `ψ_{E/F}(x) = x` for every `x ≤ μ`.
6. **The target** (`herbrandPsiTruncation`). Given `-1 ≤ x ≤ μ`, we have `-1 ≤ μ`, and
   Step 5 applies.

The auxiliary results prove slightly more than the target. Steps 3 and 5 hold for every
`x ≤ μ`, not only for `x ≥ -1`, because `ψ` and `φ` are the identity on `(-∞, 0]`. They
need no sign condition on the level `v₀` or `μ` beyond `-1 ≤ μ` in Step 5.

## Axioms

`#print axioms`-style inspection of `herbrandPsiTruncation` reports only `propext`,
`Classical.choice` and `Quot.sound`.
