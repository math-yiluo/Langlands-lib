# Lifting root filtration jumps of non-multipliable relative roots

Module `Langlands.Geometry.Building.RootJumpLiftNonMultipliable`.

This module defines the predicate `IsRootFiltrationJump` ("`r` is a filtration jump of the
root `a`") and proves that filtration jumps of a relative root `α` lift to filtration jumps of
an absolute root restricting to `α`, when `2α` is not a relative root. This is internal
infrastructure for Task 6577, the proof of
`Langlands.Geometry.Building.UnramifiedAffineRootRestrictionStatement`. That statement
formalizes Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition
9.4.28. Its existence part (1) says every relative affine root is the restriction of an
absolute affine root. In Task 6577's reduction an affine root vanishing at a point is a
filtration jump at value `0`, so the lemma here gives part (1) for non-multipliable `α`.
KP prove 9.4.28 through parahoric group schemes (their Proposition 9.4.23). The route here
is different and is not in the book: it uses the Library's description of the restricted
filtration through coordinates in the upper root groups. The lemmas hold for any field
extension `K/k` and any real level `r`, more generally than Task 6577 needs (there `K` is
the maximal unramified extension and the level is `0`).

## Setting

`k ⊆ K` are fields, `G` is a smooth affine group scheme over `k`, `i : S → G` is a closed
split torus with relative roots `Φ(S) = relativeRoots i`, and `G_K`, `S_K`, `i_K`, `a_K`
are the base changes along `algebraBaseMap k K`. Over `K`, `j : T → G_K` is a split torus
with opposite factor pairs (`hE`), `φ` is a root-datum valuation for `(G_K, T)` (`hφ`), and
`f : S_K → T` is a torus map with `groupHom f ≫ j = i_K` (`hfactor`). The family
`ψ = torusFieldRestrictedRootFunctionFamily hS hT hE hφ f` is the Library's restriction of
`φ` to `(G, S)`: torus restriction along `f`, then field restriction along `G(k) → G(K)`.
The base torus `i` is also assumed to have opposite factor pairs (`hEbase`); for a maximal
split torus of a connected reductive group this comes from `rootRankOneFactorization`.

## Definition

`IsRootFiltrationJump i φ a r`, for `i : S → G` over any field `k`, a family
`φ : RootFunctionFamily S G`, a character `a` and `r : ℝ`, is the proposition

`U_{a,φ,r} ⊈ U_{a,φ,r+} · U_{2a}(k)`,

where `U_{a,φ,r} = rootFiltration i φ a r` (points of `U_a(k)` with value `≥ r`),
`U_{a,φ,r+}` is the set of points of `U_a(k)` with value `> r`, and
`U_{2a}(k) = doubleRootGroupPoints i a` (the rational points of `U_{2a}` if `2a` is a root,
trivial otherwise). The product is the pointwise product of subsets of `G(k)`.

Provenance: when `φ` is the family of a point `x` of an apartment, this is the condition that
KP Definition 6.3.4 (printed pp. 217–218) imposes on an affine functional with derivative `a`
and value `r` at `x` for it to be an affine root: `U_ψ ⊈ U_{ψ+} · U_{2a}(k)`. The predicate
names that condition at a single root and level, which is the form used in the zero-jump
statements of Task 6577's reduction. This module does not prove an identification with the
Library's `KPApartmentData.affineRoots`.

## Theorems

- `exists_gt_forall_le_of_forall_lt`: if finitely many extended reals `q l` all lie strictly
  above a real `r`, some real `s > r` lies below every `q l`. (Elementary; take `s` between
  `r` and the finite infimum.)

- `multiplier_eq_one_of_two_nsmul_not_mem`: if `α ∈ Φ(S)`, `2α ∉ Φ(S)`, `χ` is a root of
  `(G_K, T)` and `f ≫ χ = m • α_K` with `m > 0`, then `m = 1`.

- `doubleRootGroupPoints_eq_bot_of_two_nsmul_not_mem`: under the same hypotheses, if
  `f ≫ χ = α_K` then `2χ` is not a root of `(G_K, T)`, so `U_{2χ}(K)` is trivial.

- `exists_rootJump_lift_of_two_nsmul_not_mem` (main theorem): if `α ∈ Φ(S)`, `2α ∉ Φ(S)`
  and `IsRootFiltrationJump i ψ α r`, then there is `χ ∈ relativeRoots j` with
  `f ≫ χ = α_K` and `IsRootFiltrationJump j φ χ r`.

## Proofs

`multiplier_eq_one_of_two_nsmul_not_mem`: the character lattice of the split torus `S` is
torsion-free (it embeds in its rationalization, `hS.character_toRat_injective`), so
`m • α ≠ 0`; base change of characters is an injective additive map
(`characterLattice.baseChangeEquiv`), so `f ≫ χ = (m • α)_K` is nonzero and hence a relative
root of `groupHom f ≫ j = i_K` (`rootRestriction`). By `mem_roots_baseChange_iff`,
`m • α ∈ Φ(S)`. The Library bound `RelativeRoot.HasOppositeFactorPairs.nat_multiple_le_two`
gives `m ≤ 2`, and `m = 2` is excluded by `2α ∉ Φ(S)`.

`doubleRootGroupPoints_eq_bot_of_two_nsmul_not_mem`: if `2χ` were a root, then
`f ≫ 2χ = 2 • α_K` (`Preadditive.comp_nsmul`), so the previous lemma gives `2 = 1`.

Main theorem:

1. Unfold `IsRootFiltrationJump` and pick `u ∈ U_{α,ψ,r}` outside
   `U_{α,ψ,r+} · U_{2α}(k)`. Since `U_{2α}(k)` is trivial, `u = u · 1` would lie in that
   product if `r < ψ_α(u)`, so `¬ (r < ψ_α(u))`.
2. By `rootFiltration_torusFieldRestrictedRootFunctionFamily`, for every `s`,
   `s ≤ ψ_α(u)` iff the extension `u_K` of `u` lies in the Library's canonical depth subgroup
   `torusRestrictedRootDepthSubgroup hφ f α_K s`.
3. `u_K` lies in the root group of `α_K` for `groupHom f ≫ j`
   (`torusRestrictedRootDepthSubgroup_le_rootGroupPoints`). Enumerate the selected
   indivisible roots `a_1, …, a_n` of `(G_K, T)` over `α_K` with multipliers
   `f ≫ a_l = m_l • α_K` (`exists_torusRestrictionRootDepth_enumeration`) and write
   `u_K = ∏ X_l` with `X_l ∈ U_{a_l}(K)`
   (`RelativeRoot.mem_subgroup_comp_torusHom_iff_existsUnique_rootPointsProduct`).
   By `multiplier_eq_one_of_two_nsmul_not_mem`, every `m_l = 1`.
4. `mem_torusRestrictedRootDepthSubgroup_iff_coordinate_bounds` then says: `u_K` has depth
   `≥ s` iff `s ≤ φ_{a_l}(X_l)` for every `l`.
5. If every `φ_{a_l}(X_l) > r`, `exists_gt_forall_le_of_forall_lt` gives `s > r` below all
   of them, so by steps 2 and 4 `s ≤ ψ_α(u)`, contradicting step 1. Hence some `l` has
   `φ_{a_l}(X_l) ≤ r`, while `r ≤ φ_{a_l}(X_l)` by step 4 at level `r`.
6. Take `χ = a_l`; then `f ≫ χ = α_K` and `X_l ∈ U_{χ,φ,r}`. If `X_l = v · d` with
   `v ∈ U_{χ,φ,r+}` and `d ∈ U_{2χ}(K)`, then `d = 1` by
   `doubleRootGroupPoints_eq_bot_of_two_nsmul_not_mem`, so `X_l = v` has value `> r`,
   contradicting step 5.

## Scope

No Galois fixedness of the point and no unramifiedness of `K/k` are used: when `2α` is not a
relative root, the restricted filtration of `U_α(k)` is the preimage of a filtration of
`U_{α_K}(K)` whose depth is the minimum of the coordinate values, so a jump of `α` is directly
a jump of one coordinate root. The case `2α ∈ Φ(S)` is not covered: there the `U_{2α}`
factor has to be handled by a Galois descent argument, which this module does not provide.
