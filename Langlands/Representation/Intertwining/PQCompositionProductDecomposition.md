# Renard VII.3.5 (i): the product decomposition `V₁₃ = V₁₂ V₂₃`

Author: Worker 102. Module
`Langlands.Representation.Intertwining.PQCompositionProductDecomposition`, namespace
`Langlands.Aubert.General.RepresentedParabolic`. Universe parameter `u`.

The module proves

```
theorem pqCompositionProduct : PQCompositionProductStatement.{u}
```

without extra hypotheses. `PQCompositionProductStatement` is premise (2) of the published
reduction `pqIntertwiningComposition_of_reductions` of Renard VII.3.5 (i), stated in
`Langlands.Representation.Intertwining.PQIntertwiningCompositionReduction`. It concerns three
represented parabolics `Pⱼ = M Nⱼ` of a connected reductive group `G` over a nonarchimedean local
field `F`, all with the same Levi embedding `l₁ ≫ p₁ : M → G`, together with opposite parabolics
`P̄ⱼ = M N̄ⱼ` (`pointImage pⱼ ⊓ pointImage pbⱼ = pointImage (l₁ ≫ p₁)`), and a split component
`a : A → M`. Set

- `V₁₂ = N̄₁(F) ∩ N₂(F)`, `V₂₃ = N̄₂(F) ∩ N₃(F)` and `V₁₃ = N̄₁(F) ∩ N₃(F)`;
- `d(P, P')` = the number of indivisible relative roots of `i = a ≫ l₁ ≫ p₁` that are roots of
  both `N` and `N̄'`.

Assume `d(P₁, P₂) + d(P₂, P₃) = d(P₁, P₃)`. The statement asserts that there is a homeomorphism
`e : V₁₂ × V₂₃ ≃ₜ V₁₃` with `e(w, u) = w u` in `G(F)`.

The proof does not use the hypothesis `d(P₁, P₂) = 1`, the hypotheses
`IsIso (subgroupMultiplication _ _)`, or the instances `LocallyCompactSpace G(F)` and
`NonarchimedeanGroup G(F)`. They are binders of the published statement.

The proof uses lemma `RelativeRoot.dynamicUnipotent_inf_le_of_positiveRoots`, which is new in
`Langlands.GroupScheme.Rational.DynamicUnipotentIntersectionRoots`. That module is submitted with
this one and has its own Markdown.

## Notation

`i = a ≫ l₁ ≫ p₁ : A → G`. For a cocharacter `λ` of `A`, `U(λ)` is the group of rational points
of the dynamic radical `Dynamic.unipotent (groupHom λ ≫ i)` and `Z(λ)` that of the dynamic
centralizer. `⟨β, λ⟩` is `latticePairing A β λ`. `pos(λ)` is
`positiveRelativeRoots i λ = {β ∈ relativeRoots i | 0 < ⟨β, λ⟩}`, and `I` is
`RelativeRoot.indivisibleRoots i`.

## Generic lemmas

- `union_subset_of_ncard_add_eq`: if `X ⊆ Y₁ ∪ Y₂` with `Y₁`, `Y₂` finite and disjoint and
  `|Y₁| + |Y₂| = |X|`, then `Y₁ ∪ Y₂ ⊆ X`. The union has cardinality `|X|`, so the inclusion
  `X ⊆ Y₁ ∪ Y₂` of finite sets is an equality (`Set.eq_of_subset_of_ncard_le`).
- `infChartHomeomorph` (with `infChartHomeomorph_apply`): let `K, A, B, C` be subgroups of a
  topological group `Γ`. Let `e : A.subgroupOf C × B ≃ₜ C` be a homeomorphism given by
  multiplication. Assume `K ⊓ A ≤ C` and `B ≤ K`. Then multiplication is a homeomorphism
  `(K ⊓ A) × B ≃ₜ K ⊓ C`.
  - The forward map is the restriction of `e`. Its values lie in `K` because both factors do.
  - The inverse sends `g ∈ K ⊓ C` to the pair `e⁻¹(g)`. Its first factor equals `g z⁻¹`, where
    `z ∈ B ≤ K` is the second factor, so it lies in `K ⊓ A`.
  - Continuity follows from that of `e` and `e⁻¹` and of the subtype maps.
- `exists_mul_homeomorph_of_chart`: the same conclusion for subgroups `V₁ = K ⊓ A`, `V₂ = B`,
  `V₃ = K ⊓ C` given up to equality, as an existence statement.
- Pairing arithmetic: `latticePairing_neg_right` (`⟨β, -λ⟩ = -⟨β, λ⟩`),
  `latticePairing_nsmul_left` (`⟨n • β, λ⟩ = n ⟨β, λ⟩`), and `nat_mul_pos_iff`,
  `nat_mul_neg_iff` (for `n > 0`, the sign of `n x` is the sign of `x`).

## One parabolic and its opposite: `exists_oppositePair_cocharacter`

Let `P = M N` (morphisms `p, l, r`) and `P̄ = M N̄` (morphisms `pb, lb, rb`) be represented
parabolics with `l ≫ p = m₀ = lb ≫ pb` and `P(F) ∩ P̄(F) = M(F)`. The lemma gives a cocharacter
`λ` of `A` such that:

1. `subgroupRelativeRoots (a ≫ m₀) N = pos(λ)` and `subgroupRelativeRoots (a ≫ m₀) N̄ = pos(-λ)`;
2. `N(F) = U(λ)` and `N̄(F) = U(-λ)`;
3. `range m₀ = Z(λ)` as subgroup functors;
4. `⟨β, λ⟩ ≠ 0` for every relative root `β` of `a ≫ m₀`.

Proof. `parabolicRootPresentationExistence` gives root presentations `R` of `(p, l)` and `S` of
`(pb, lb)` relative to `a`. Take `λ = R.splitComponentCocharacter`.

- Roots of `N`: `R.subgroupRelativeRoots_radical`.
- Roots of `N̄`: `S.subgroupRelativeRoots_radical` describes them by the sign of
  `S.splitComponentCocharacter`. `R.opposite_componentRoot_signs S`, which uses
  `P(F) ∩ P̄(F) = M(F)`, turns this into negativity on `λ`.
- `N(F) = U(λ)`: `R.range_comp_radical_eq`.
- `N̄(F) = U(-λ)`: `pointImage_opposite_radical_eq_dynamic` (with `parabolicDynamic` and
  `oppositeDynamicParabolicUniqueness`) identifies `N̄(F)` with the radical of the opposite
  cocharacter, and `groupHom_neg_comp_eq_oppositeCocharacter` rewrites that as `-λ`.
- `range m₀ = Z(λ)`: `R.levi_eq_splitComponentCocharacter`.
- Item 4: suppose `⟨β, λ⟩ = 0`. `relativeRoots_centralizer_factor` (for `dynamicLie`) puts `β`
  among the relative roots of `a : A → M`, since `M = Z(λ)`. But `A` is central in `M`
  (`ha.1.2`), so every root of `a` restricts to zero (`root_restrict_eq_zero_of_isCentral`),
  while roots are nonzero.

## The main proof

Apply `exists_oppositePair_cocharacter` to `(P₁, P̄₁)`, `(P₂, P̄₂)`, `(P₃, P̄₃)` with
`m₀ = l₁ ≫ p₁`, getting `λ₁, λ₂, λ₃`. Unfolding `d` and rewriting by item 1, the hypothesis
becomes `|Y₁| + |Y₂| = |X|` with

- `Y₁ = (pos(λ₁) ∩ I) ∩ (pos(-λ₂) ∩ I)`, the indivisible roots with `λ₁ > 0`, `λ₂ < 0`;
- `Y₂ = (pos(λ₂) ∩ I) ∩ (pos(-λ₃) ∩ I)`, those with `λ₂ > 0`, `λ₃ < 0`;
- `X = (pos(λ₁) ∩ I) ∩ (pos(-λ₃) ∩ I)`, those with `λ₁ > 0`, `λ₃ < 0`.

The proof continues in four steps.

1. **Counting.** `X ⊆ Y₁ ∪ Y₂`: for `β ∈ X`, `⟨β, λ₂⟩ ≠ 0` by item 4, and its sign decides
   between `Y₁` and `Y₂`. `Y₁` and `Y₂` are disjoint, by the sign of `λ₂`. Both are finite,
   because relative roots of a split torus are finite (`IsSplitTorus.finite_relativeRoots`). So
   `union_subset_of_ncard_add_eq` gives `Y₁ ∪ Y₂ ⊆ X`.
2. **`V₁₂ ≤ N₃(F)`, i.e. `U(-λ₁) ∩ U(λ₂) ≤ U(λ₃)`.** Apply
   `dynamicUnipotent_inf_le_of_positiveRoots` with `(mu, ν, κ) = (-λ₁, λ₂, λ₃)`. Let `β` be a
   root with `⟨β, λ₂⟩ > 0` and `⟨β, λ₁⟩ < 0`, and suppose `⟨β, λ₃⟩ ≤ 0`, hence `< 0` by item 4.
   `RelativeRoot.exists_indivisiblePositiveRoot_ray` writes `β = n • α` with `n > 0` and `α`
   indivisible with `⟨α, λ₂⟩ > 0`. Then `⟨α, λ₁⟩ < 0` and `⟨α, λ₃⟩ < 0`. So `α ∈ Y₂ ⊆ X`, which
   forces `⟨α, λ₁⟩ > 0`, a contradiction.
3. **`V₂₃ ≤ N̄₁(F)`, i.e. `U(-λ₂) ∩ U(λ₃) ≤ U(-λ₁)`.** Apply the lemma with
   `(mu, ν, κ) = (-λ₂, λ₃, -λ₁)`. Let `β` be a root with `⟨β, λ₃⟩ > 0` and `⟨β, λ₂⟩ < 0`, and
   suppose `⟨β, λ₁⟩ ≥ 0`, hence `> 0`. The ray along `λ₃` gives `β = n • α` with `α` indivisible,
   `⟨α, λ₃⟩ > 0`, `⟨α, λ₂⟩ < 0` and `⟨α, λ₁⟩ > 0`. So `α ∈ Y₁ ⊆ X`, which forces
   `⟨α, λ₃⟩ < 0`, a contradiction.
4. **The chart.** Put `χ = groupHom λ₃ ≫ i` and `ψ = groupHom λ₂ ≫ i`. Their centralizers have
   the same rational points, since both equal `range (l₁ ≫ p₁)` by item 3.
   `Plancherel.StandardIntertwining.OppositeCharts.secondChart` then gives a homeomorphism
   `U(ψ).subgroupOf U(χ) × (U(ψ⁻¹) ∩ U(χ)) ≃ₜ U(χ)`. It is multiplication by definition
   (`fun _ => rfl`), and `U(ψ⁻¹) = U(-λ₂)` by `groupHom_neg_comp_eq_oppositeCocharacter`.
   `exists_mul_homeomorph_of_chart` with `K = U(-λ₁)`, `A = U(λ₂)`, `B = U(-λ₂) ∩ U(λ₃)` and
   `C = U(λ₃)` uses steps 2 and 3. With item 2, `V₁₂ = K ∩ A`, `V₂₃ = B` and `V₁₃ = K ∩ C`,
   which yields the required homeomorphism.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026. Literature ID `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Proposition VII.3.5 is on
printed p.237 / PDF p.243. In the proof of (i), printed p.239 / PDF p.245, Renard says the
hypothesis `d(P₁, P₃) = d(P₁, P₂) + d(P₂, P₃)` translates into
`N̄₁ ∩ N₃ = (N̄₁ ∩ N₂)(N̄₂ ∩ N₃)`. He gives no further argument.

The argument here is derived. It supplies that translation through the root computations above,
together with an existing chart for `N₃(F)`, and is not taken from Renard. All
algebraic-group inputs (root presentations, opposite parabolics, dynamic radicals, root rays and
the chart) are already in the Library, apart from lemma (C),
`RelativeRoot.dynamicUnipotent_inf_le_of_positiveRoots`.
