# Renard VII.3.5 (i): inheritance of regularity

Author: Worker 102. Module `Langlands.Representation.Intertwining.PQCompositionLeviIntersection`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u` (the field)
and `v` (the representation).

## Statements proved

- `pqCompositionRegularity : PQCompositionRegularityStatement.{u, v}`. This is premise (4) of
  the published reduction `pqIntertwiningComposition_of_reductions` of Renard VII.3.5 (i)
  (module `PQIntertwiningCompositionReduction`): under the hypotheses of VII.3.5 (i), every
  `P₁P₃`-regular `σ` is `P₂P₃`-regular and `P₁P₂`-regular. This is the recorded proof.
- `pqCompositionBruhat : PQCompositionBruhatStatement.{u}`, the published Bruhat-order input
  (module `PQCompositionRegularityReduction`).
- `pqCompositionLeviIntersection`, the equality part of `PQCompositionBruhatStatement`, stated
  directly as a theorem.

`pqCompositionRegularity` is `pqCompositionRegularityOfBruhat pqCompositionBruhat`, where
`pqCompositionRegularityOfBruhat` is the published reduction. The module adds no definitions.
It uses the lemmas of `PQCompositionBruhatOrder`, submitted with it.

## Notation

`G` is connected reductive over a nonarchimedean local field `F = k`. `P₁ = MN₁`, `P₂ = MN₂`,
`P₃ = MN₃` are parabolic subgroups with the same Levi embedding `m₀ = l₁ ≫ p₁`. `P̄ⱼ = MN̄ⱼ` are
opposite parabolics with `Pⱼ(F) ∩ P̄ⱼ(F) = M(F)`. `a : A ⟶ M` is a split component. The root
distances satisfy `d(P₁, P₂) + d(P₂, P₃) = d(P₁, P₃)` and `d(P₁, P₂) = 1`. For a cocharacter `ν`
of `A`, `P(ν)`, `Z(ν)`, `U(ν)` are the dynamic parabolic, centralizer and radical of
`ν ≫ a ≫ m₀` (as subgroup functors of `G`).

## Generic lemmas

- `orbit_add_nsmul_of_mem_centralizer`, using the published
  `Dynamic.orbit_add_of_mem_centralizer` from `StandardRestrictedConjugation`: for a point `g` (on any
  test scheme) centralizing a cocharacter `ζ` of a torus `T ⟶ G`, the conjugation orbits of
  `g` under `ν` and `ν + n ζ` agree. Hence (`mem_parabolic_add_nsmul_iff`,
  `mem_unipotent_add_nsmul_iff`) on points of `Z(ζ)`, membership in `P(ν)` and in `P(ν + n ζ)`
  agree, and so do membership in `U(ν)` and in `U(ν + n ζ)`.
- `mem_levi_of_mem_parabolic_of_conj`: over a nonarchimedean local field, let `z ∈ P(χ)(F)`
  satisfy `z⁻¹ χ(s) z ∈ Z(χ)(F)` for every `s ∈ F^×`. Then `z ∈ Z(χ)(F)`. Proof: write
  `z = l u` with `l ∈ Z(χ)(F)` and `u ∈ U(χ)(F)` (`RationalPoint.existsUnique_levi_mul_unipotent`).
  `χ(s)` commutes with `l`, so `u⁻¹ χ(s) u ∈ Z(χ)(F)`. The commutator `χ(s)⁻¹ (u⁻¹ χ(s) u)` is then
  in `Z(χ)(F) ∩ U(χ)(F) = 1`. So `u` commutes with every `χ(s)`, and `u = 1` by contraction
  (`eq_one_of_mem_unipotentPoints_of_commute`).
- `exists_dynamic_oppositePair_cocharacter`: for a parabolic `P = MN` and an opposite
  `P̄ = MN̄`, there is a cocharacter `λ` of `A` with
  - `roots(N) = {λ > 0}` and `roots(N̄) = {λ < 0}`;
  - `P = P(λ)`, `N = U(λ)` and `M = Z(λ)` as subgroup functors;
  - `⟨β, λ⟩ ≠ 0` for every root `β`;
  - the relative roots of `a ≫ m₀` stable under negation.

  These come from a parabolic root presentation (`parabolicRootPresentationExistence`,
  `parabolic_eq_splitComponentCocharacter`, `range_comp_radical_eq`,
  `levi_eq_splitComponentCocharacter`, `opposite_componentRoot_signs`,
  `neg_mem_componentRelativeRoots`). This is the scheme-level analogue of
  `exists_oppositePair_cocharacter` from `PQCompositionProductDecomposition`, with the same proof.

## Proof of `pqCompositionLeviIntersection`

Let `z` satisfy `P₁zP₂ <_{P₁P₂} P₁P₂`, with a maximal split torus `T` of `G` inside `M` and
inside `zMz⁻¹`. Take `λ₁, λ₂, λ₃` from `exists_dynamic_oppositePair_cocharacter`.

1. **Roots.** The hypothesis `d(P₁, P₂) + d(P₂, P₃) = d(P₁, P₃)` gives, as in
   `pqCompositionProduct`, that the indivisible roots of `N₁ ∩ N̄₂` and of `N₂ ∩ N̄₃` are roots of
   `N₁ ∩ N̄₃`. By `d(P₁, P₂) = 1` there is exactly one indivisible root `α` with
   `⟨α, λ₁⟩ > 0 > ⟨α, λ₂⟩`, and then `⟨α, λ₃⟩ < 0`. Every root `β` with
   `⟨β, λ₁⟩ > 0 > ⟨β, λ₂⟩` is a positive multiple of `α` (`hray`, via
   `RelativeRoot.exists_indivisiblePositiveRoot_ray`).
2. **The cocharacter of `L`.** Put `c₁ = ⟨α, λ₁⟩ > 0`, `c₂ = -⟨α, λ₂⟩ > 0` and
   `μ = c₂ λ₁ + c₁ λ₂`, so `⟨α, μ⟩ = 0`. Every root nonnegative on `λ₁` or on `λ₂` is nonnegative on
   `μ`. (Negation stability is used for roots positive on `λ₂` and negative on `λ₁`.) For a
   root `β` with `⟨β, μ⟩ = 0`, `±β` is a positive multiple of `α`, so `⟨β, λ₂⟩` and `⟨β, λ₃⟩` have
   the same sign. Renard's `L` is `Z(μ)`, and `Q = LU` is `P(μ)`.
3. **A dominant shift.** Bound `|⟨β, λ₂⟩| + |⟨β, λ₃⟩| ≤ B` on the finitely many roots and let
   `n = B + 1`. Then `⟨β, λ₂ + n μ⟩` and `⟨β, λ₃ + n μ⟩` have the same strict sign for every root
   `β`. The Library root criteria `RelativeRoot.parabolic_le_iff_nonnegative_rootSupport` (with
   `dynamicConnected`) and `RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth` give
   `P(λ₂ + n μ) = P(λ₃ + n μ)` and `U(λ₂ + n μ) = U(λ₃ + n μ)`.
4. **`z ∈ L(F)`.** By the same criterion, `P₁ = P(λ₁) ≤ P(μ)` and `P₂ = P(λ₂) ≤ P(μ)`. The
   points `P(μ)(F)` form a closed subgroup (`isClosed_dynamic_parabolic`). So
   `z ∈ closure(P₁(F) P₂(F)) ⊆ P(μ)(F)` (`bruhatLE_mk_one_iff`). Also `M ≤ Z(μ)`, since `a` is
   central in `M` (`isCentral_comp_iff_le_dynamicCentralizer`). And `z⁻¹ μ(s) z ∈ M(F)`
   (`conj_cocharPoint_mem_of_torus`). So `mem_levi_of_mem_parabolic_of_conj` gives
   `z ∈ Z(μ)(F)`.
5. **The equalities.** For a point `w` of `Z(μ)` on any test scheme,
   `w ∈ P₂ ⟺ w ∈ P(λ₂ + n μ) ⟺ w ∈ P(λ₃ + n μ) ⟺ w ∈ P₃` (steps 3 and the generic lemmas),
   and likewise `w ∈ N₂ ⟺ w ∈ N₃`. Let `y` be a point of `M`, and `c` the constant point of `z`.
   `y` lies in `range (p₂ ≫ inn z)` iff `c⁻¹ y c ∈ P₂`
   (`MaximalTorusParameterExistence.mem_range_comp_innerIso_iff`). Since `c` and `y` lie in
   `Z(μ)`, so does `c⁻¹ y c`. So `M ∩ zP₂z⁻¹ = M ∩ zP₃z⁻¹`, and in the same way
   `M ∩ zN₂z⁻¹ = M ∩ zN₃z⁻¹`, as subgroup functors.

This is Renard's argument (printed pp.237–238 / PDF pp.243–244): `P₁P₂ ⊆ Q = LU`, so `w` lies
in `L`, and `M ∩ w·P₃ = M ∩ w·(P₃ ∩ L) = M ∩ w·(P₂ ∩ L) = M ∩ w·P₂`. The differences are:
- Renard uses the Bruhat decomposition of `L` to place `w` in `W_L`. Here a contraction argument
  shows `z ∈ L(F)` for the torus-adapted representative `z`.
- `P₃ ∩ L = P₂ ∩ L` is checked through the dynamic shift `λⱼ + n μ` and the root criteria.
- The unipotent radicals are compared as well.

## Proof of `pqCompositionBruhat`

Take `λ₁, λ₂, λ₃` from `exists_oppositePair_cocharacter` and obtain
`U(-λ₁)(F) ∩ U(λ₂)(F) ≤ U(λ₃)(F)`, i.e. `(N̄₁ ∩ N₂)(F) ≤ N₃(F)`, from the root hypothesis and
`RelativeRoot.dynamicUnipotent_inf_le_of_positiveRoots`, as in `pqCompositionProduct`. Then
`P₂(F) ⊆ P₁(F) P₃(F)`. Indeed, `x = m n ∈ P₂(F)` with `n ∈ U(λ₂)(F)`, and the chart for
`(λ₂, λ₁)` (`exists_mul_eq_of_secondChart`) writes `n = b c` with `b ∈ N₁(F)` and
`c ∈ (N̄₁ ∩ N₂)(F) ≤ N₃(F)`. Now `bruhatLT_mk_one_of_subset_mul` with the core lemma
`mem_levi_of_mem_mul_of_torus` gives item 1 and the Bruhat part of item 2.
`pqCompositionLeviIntersection` gives the two equalities of item 2.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, literature ID `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Proposition VII.3.5 (i),
printed p.237 / PDF p.243; the regularity part of the proof is on printed pp.237–238 /
PDF pp.243–244.
