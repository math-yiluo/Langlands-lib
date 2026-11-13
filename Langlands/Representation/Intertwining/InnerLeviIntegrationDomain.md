# The integration domain of Renard VII.3.5 (ii) lies in the Levi

Author: Worker 115. Module
`Langlands.Representation.Intertwining.InnerLeviIntegrationDomain`.

This module is supporting material for Renard VII.3.5 (ii) (David Renard,
*Représentations des groupes réductifs p-adiques*, French version of 9 July 2026,
VII.3.5, printed pp.237–240 / PDF pp.243–246). The setting has:

- represented parabolics `P₁ = MN₁` and `P₂ = MN₂` of `G`;
- an opposite `P̄₁ = MN̄₁` of `P₁`;
- a represented parabolic `Q = LU` with `P₁(F), P₂(F) ⊂ Q(F)`;
- parabolics `P₁' = MN₁'`, `P₂' = MN₂'` and `P̄₁' = MN̄₁'` of `L`, where `Pᵢ'(F)` is
  `Pᵢ(F) ∩ L(F)` inside `G(F)`.

The main result shows that `V = N̄₁(F) ∩ N₂(F)` is the image of
`V' = N̄₁'(F) ∩ N₂'(F)` under the embedding `emb : L(F) → G(F)`. Renard uses this without
comment when he writes the integral over `N̄₁ ∩ N₂` as an integral over `N̄₁' ∩ N₂'` (both
lie in `L`). The module also identifies `V'` with `V` as topological groups. The results
are internal helpers derived for this proof; the literature does not state them separately.

## Declarations

- `Dynamic.unipotent_isStable_conjugation_of_range_le_centralizer`: let `τ` be a
  cocharacter whose image lies in the centralizer `Z(χ)` of another cocharacter `χ`. Then
  the dynamic unipotent subgroup `U(χ)` is stable under conjugation by `τ`. Proof: a point
  of `range τ` lies in `Z(χ)`, and `Z(χ)` normalizes `U(χ)`
  (`centralizer_le_normalizer_unipotent`).
- `map_mem_pointImage_comp`, `mem_pointImage_of_map_mem_comp`: these handle images of
  rational points along a composite `f ≫ g`. The first sends `pointImage f` into
  `pointImage (f ≫ g)`. The second cancels a monomorphism `j`: if the image of `x` lies in
  `pointImage (f ≫ j)`, then `x ∈ pointImage f`.
- `pointImage_opposite_radical_eq_dynamic_of_points`: a variant of the Library lemma
  `pointImage_opposite_radical_eq_dynamic`. Here the parabolic `P` is only known to agree
  with the dynamic parabolic `P(χ)` on rational points, and `M = Z(χ)`. Under these
  hypotheses, the radical of an opposite `P̄` (with `P(F) ∩ P̄(F) = M(F)`) has as rational
  points the opposite unipotent `U(χ⁻¹)(F)`. Proof:
  `DynamicLeviConjugacy.exists_cocharacter_parabolic_levi` gives a cocharacter `χ'`
  realizing `P̄` and `M`. Then `χ` and `χ'` have the same centralizer, and
  `P(χ)(F) ∩ P(χ')(F) = M(F)`. `oppositeDynamicParabolicUniqueness` gives
  `U(χ') = U(χ⁻¹)`, and `pointImage_radical_eq_dynamic` identifies the radical of `P̄` with
  `U(χ')` on points.
- `oppositeRadical_inf_le_levi`: `N̄₁(F) ∩ Q(F) ⊆ L(F)`. Proof: realize `P₁ = P(χ)`,
  `M = Z(χ)` and `Q = P(τ)`, `L = Z(τ)` by cocharacters. Since `χ` takes values in
  `M ⊆ L = Z(τ)`, `τ` commutes with `χ⁻¹`, so `U(χ⁻¹)` is stable under conjugation by `τ`
  (first lemma). The stable-intersection decomposition
  `Dynamic.inf_parabolic_eq_mul_of_isStable` writes a point of `U(χ⁻¹)(F) ∩ P(τ)(F)` as
  `a n` with `a ∈ Z(τ)(F)` and `n ∈ U(χ⁻¹)(F) ∩ U(τ)(F)`. By
  `nestedParabolicPointDecomposition`, `U(F) ⊆ P₁(F)`. So `n` lies in
  `U(χ⁻¹)(F) ∩ P(χ)(F) = 1` (`Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic`),
  and the point is `a ∈ L(F)`.
- `mem_innerOppositeRadical_iff`: for `x ∈ L(F)`, `x ∈ N̄₁'(F)` if and only if
  `emb x ∈ N̄₁(F)`. Proof: `χ` factors through `L` as `χL`, because its image lies in
  `M ⊆ L` and `L → G` is a closed subgroup (`IsRepresentedBy.factorHom_comp`). The dynamic
  subgroups of `χL` are the pullbacks along `L → G` of those of `χ`
  (`Dynamic.parabolic_eq_comap_of_isClosedSubgroup` and the centralizer and unipotent
  analogues). With `P₁'(F) = P₁(F) ∩ L(F)`, this gives `P₁'(F) = P(χL)(F)` and
  `M = Z(χL)`. The previous variant then gives `N̄₁'(F) = U(χL⁻¹)(F)`, while
  `N̄₁(F) = U(χ⁻¹)(F)` by `pointImage_opposite_radical_eq_dynamic`.
- `innerIntegrationDomain_eq_map`: the subgroup `N̄₁(F) ∩ N₂(F)` of `G(F)` equals the image
  of `N̄₁'(F) ∩ N₂'(F)` under `rationalPoints.map (lQ ≫ q)`. Proof:
  `nestedParabolicPointDecomposition` for `P₂` gives `N₂'(F) = L(F) ∩ N₂(F)`. A point `y` of
  `N̄₁(F) ∩ N₂(F)` lies in `Q(F)` (as `N₂(F) ⊆ P₂(F) ⊆ Q(F)`), so in `L(F)` by
  `oppositeRadical_inf_le_levi`. Write it as `y = emb x`. Then `x ∈ N̄₁'(F)` by
  `mem_innerOppositeRadical_iff`, and `x ∈ N₂'(F)` by the radical identity and injectivity
  of `emb`. The converse inclusion uses the same two facts.
- `exists_continuousMulEquiv_of_isEmbedding`: if a group homomorphism `f : A →* B` is a
  topological embedding and `K = f(H)` for a subgroup `H`, then there is `e : H ≃ₜ* K` with
  `e x = f x`. Proof: `Subgroup.equivMapOfInjective`; continuity in both directions holds
  because `f` is inducing.
- `isEmbedding_leviPoints`: the point map `L(F) → G(F)` is a topological embedding. Here
  `L(F)` has the topology `leviPointTopology` and `G(F)` the canonical point topology. The
  map is the subtype inclusion composed with the homeomorphism `leviPointsEquiv`.
- `exists_leviSubgroupEquiv`: for subgroups `V' ⊆ L(F)` and `V = emb(V') ⊆ G(F)`, there is
  an isomorphism of topological groups `e : V' ≃ₜ* V` with `e x = emb x`. This combines the
  last two lemmas.
