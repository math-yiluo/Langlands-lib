# Regularity transfer of Renard VII.3.5 (iii)

Lean module: `Langlands.Representation.Intertwining.PQOuterLeviRegularity`.

This module proves the regularity part of Renard VII.3.5 (iii) (Renard 2026, French version
of 9 July 2026, printed pp.239–240 / PDF pp.245–246): if `X = i_{P'}^L(σ)` is
`Q₁Q₂`-regular for the split component `A_L` of `L`, then `σ` is `P₁P₂`-regular for any split
component `A` of `M`. Renard argues with the geometric lemma and faithfulness of parabolic
induction. The Lean proof takes a different, more direct route: it pushes both ideals of the
regularity condition `I_X + I^{Q₁Q₂}_X = ℂ[A_L(F)]` forward along a homomorphism
`A_L(F) → A(F)`. The auxiliary lemmas are internal.

## Declarations

### Group algebras (namespace `Langlands`)

- `asAlgebraHom_mapDomain_apply`: let `ρ₁`, `ρ₂` be complex representations of monoids
  `H₁`, `H₂`, let `φᵢ : Bᵢ → Hᵢ` and `κ : B₁ → B₂` be monoid homomorphisms, and let
  `Ψ : V₁ → V₂` be linear with `Ψ (ρ₁(φ₁ z) v) = ρ₂(φ₂ (κ z)) (Ψ v)`. Then for every
  `x ∈ ℂ[B₁]`, the action of `κ_* x` on `Ψ v` (through `ρ₂ ∘ φ₂`) is `Ψ` of the action of `x`
  on `v` (through `ρ₁ ∘ φ₁`). Proof: induction on `x` (`MonoidAlgebra.induction_linear`).
- `map_groupAlgebraKernel_le`: if moreover `Ψ` is surjective, then `κ_*` maps the kernel of
  `ℂ[B₁]` on `V₁` (`groupAlgebraKernel ρ₁ φ₁`) into the kernel of `ℂ[B₂]` on `V₂`.
- `sup_eq_top_of_map_le`: for a ring homomorphism `f : R → S` and ideals with `I ⊔ J = ⊤`,
  `f(I) ⊂ I'`, `f(J) ⊂ J'`, one has `I' ⊔ J' = ⊤`.

### Split components

- `exists_outer_splitComponent_factor`: let `G` be connected reductive, `P₁ = MN₁` a
  parabolic with rational Levi `l₁ : M → P₁`, `Q₁` a parabolic with rational Levi
  `lQ₁ : L → Q₁`, `P'` a parabolic of `L` with rational Levi `l' : M → P'`, with
  `l' ≫ p' ≫ lQ₁ ≫ q₁ = l₁ ≫ p₁`. For split components `a : A → M` and `aL : A_L → L` there is
  a homomorphism `f : A_L → A` with `f ≫ a ≫ l' ≫ p' = aL`.

  Proof (following the pattern of `NestedSplitComponentFactorization`): choose a cocharacter
  `ψ` of `G` with `M = Z_G(ψ)` (`exists_cocharacter_parabolic_levi`). `ψ` lies in its own
  centralizer, hence in `M` and in `L`, so it factors through `L` as `χ_L`. Since `A_L` is
  central in `L`, it centralizes `χ_L`, so `A_L → G` lands in `Z_G(ψ) = M`; the factor
  `b : A_L → M` satisfies `b ≫ l' ≫ p' = aL` (cancel the closed immersion `L → G`) and is
  central in `M` (`IsCentral.of_comp`). As `A_L` is a split torus, `b` factors through the
  split component `a` (`IsSplitComponent.exists_factor`).

### Haar moduli (generic topological group `H`)

- `closedNormalizerCharacter_eq_one_of_commute'`: the modulus of conjugation by an element
  commuting with a closed subgroup `U` is `1` (conjugation is the identity of `U`).
- `closedHalfCharacter_eq_one_of_commute`: hence `δ^{1/2}` at such an element is `1`.
- `closedInverseHalfCharacter_eq_of_eq`: `δ^{-1/2}` only depends on the value of the modulus.

### The outer Levi configuration

The section `Regularity` takes the data and hypotheses of `PQIntertwiningOuterLeviStatement`
(without the opposites), as in `PQOuterLeviOperator`. `outer_rationalPoints_map_comp_apply`
is functoriality of rational points.

- `outer_splitComponentKernel_map_le`: for `f : A_L → A` with `f ≫ a ≫ l' ≫ p' = aL`,
  `f_*(I_X) ⊂ I_σ`, where `I_X` is the kernel of `ℂ[A_L(F)]` on `X = i_{P'}^L(σ)` and `I_σ`
  that of `ℂ[A(F)]` on `σ`. Proof: evaluation at `1`, `X → σ`, is surjective
  (`normalizedInduction_eval_surjective`, continuous Levi projection). For `z ∈ A_L(F)` with
  image `y` in `L(F)`, `y` is the image of `m = a(f z) ∈ M(F)` in the Levi of `P'`, and
  `(y·φ)(1) = φ(y) = δ_{P'}^{1/2}(y) σ(m) φ(1) = σ(m) φ(1)`, since `y` is central in `L(F)`
  and so commutes with `N'(F)`. Apply `map_groupAlgebraKernel_le`.
- `outer_modulus_eq`: for `y` central in `L(F)` whose image `g` in `G(F)` lies in `M(F)`,
  `δ_{N₂}(g) = δ_{U₂}(g)`. Proof: `U₂(F) ⊂ N₂(F) ⊂ Q₂(F)` (`outer_radical₂_le`), so the
  decomposition `Q₂(F) = L(F) ⋉ U₂(F)` restricts to `N₂(F) = (L(F) ∩ N₂(F)) ⋉ U₂(F)` with
  continuous projection; `closedNormalizerCharacter_eq_mul` gives
  `δ_{N₂}(g) = δ_{L ∩ N₂}(g) δ_{U₂}(g)`, and `δ_{L ∩ N₂}(g) = 1` since `g` commutes with
  `L(F)`.
- `outer_mem_boundaryVanishing_of_stages`: if `Φ₁ f` vanishes on the boundary of
  `Q₁(F)Q₂(F)`, then `f` vanishes on the boundary of `P₁(F)P₂(F)`, where `Φ₁` is the stage
  isomorphism `i_{P₁}^G(σ) ≅ i_{Q₁}^G(X)`. Proof: the boundary of `P₁P₂` lies in that of
  `Q₁Q₂` (`outer_boundary_subset`) and `f(g) = (Φ₁ f)(g)(1)`.
- `outer_pqRegularityKernel_map_le`: `f_*(I^{Q₁Q₂}_X) ⊂ I^{P₁P₂}_σ`. Proof: `Φ₁⁻¹` followed
  by the quotient map to the `N₂(F)`-coinvariants kills the `U₂(F)`-relations because
  `U₂(F) ⊂ N₂(F)`, so it induces `Ψ₀ : r_{Q₂}(i_{Q₁}X) → r_{P₂}(i_{P₁}σ)`
  (`Jacquet.Localization.lift`). By `outer_mem_boundaryVanishing_of_stages`, `Ψ₀` maps the
  image `F^{<1̄}_{Q₁Q₂}` of the boundary-vanishing functions into `F^{<1̄}_{P₁P₂}`, so it
  induces `Ψ` between the quotients; `Ψ` is surjective because `Φ₁⁻¹` and the quotient maps
  are. For `z ∈ A_L(F)` with image `g` in `G(F)`, which is also the image of `a(f z)`, the
  normalized actions on classes are `δ_{U₂}^{-1/2}(g)[g·F]` and `δ_{N₂}^{-1/2}(g)[g·Φ₁⁻¹F]`;
  as `Φ₁⁻¹` intertwines and `δ_{U₂}(g) = δ_{N₂}(g)` (`outer_modulus_eq`), `Ψ` is
  equivariant along `f`. Apply `map_groupAlgebraKernel_le`.
- `outer_isPQRegular`: for split components `a : A → M` and `aL : A_L → L`, if `X` is
  `Q₁Q₂`-regular (`IsPQRegular` for `aL`), then `σ` is `P₁P₂`-regular (`IsPQRegular` for `a`).
  Proof: take `f` from `exists_outer_splitComponent_factor`, and apply
  `sup_eq_top_of_map_le` with `f_*` and the two inclusions above.
