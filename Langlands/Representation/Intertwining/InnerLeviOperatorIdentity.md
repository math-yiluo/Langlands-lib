# The operator identity of Renard VII.3.5 (ii)

Author: Worker 115. Module
`Langlands.Representation.Intertwining.InnerLeviOperatorIdentity`.

This module proves the operator identity of Renard VII.3.5 (ii) (David Renard,
*Représentations des groupes réductifs p-adiques*, French version of 9 July 2026,
VII.3.5, printed pp.237–240 / PDF pp.243–246). Under the regularity hypothesis it shows
`J^G_{P₂|P₁}(σ) = i_Q^G(J^L_{P₂'|P₁'}(σ))`, read through induction in stages. The lemmas
are internal helpers derived for this proof and are stated for given operators `J`, `J'`.

## Setting

The section variables fix:

- represented parabolics `P₁ = MN₁` and `P₂ = MN₂` of `G` with `P₁(F), P₂(F) ⊂ Q(F)`,
  where `Q = LU`;
- parabolics `P₁' = MN₁'` and `P₂' = MN₂'` of `L` with the same embedded Levi
  (`hM₁`, `hM₂`) and `Pᵢ'(F) = Pᵢ(F) ∩ L(F)` (`hPL₁`, `hPL₂`).

`G(F)`, `L(F)` and `M(F)` carry the canonical point topologies, and `G(F)` and `L(F)` are
assumed locally compact and nonarchimedean (instance arguments). `emb` is the point map
`rationalPoints.map (lQ ≫ q) : L(F) → G(F)`. `c(x)` is the complex value of the half
modulus `δ_U^{1/2}` of `Q(F)` at `x ∈ L(F)`. `Ψᵢ = leviInductionStagesIso` is induction in
stages `i_{Pᵢ}^G ≅ i_Q^G ∘ i_{Pᵢ'}^L` (module `LeviInductionStagesFormula`), with
`Ψᵢ(f)(g)(x) = c(x)⁻¹ f(emb(x) g)` (`leviInductionStagesIso_eval'`).

## Declarations

- `mem_innerBoundaryVanishing_of_map`: let `f ∈ F̃^{<1̄}_{P₁P₂}(σ) ⊂ i_{P₁}^G(σ)` and
  `φ ∈ i_{P₁'}^L(σ)`. If `φ(x) = 0` whenever `f(emb x) = 0`, then
  `φ ∈ F̃^{<1̄}_{P₁'P₂'}(σ)`. Proof: membership in the boundary vanishing subspace means
  vanishing on the boundary `closure(P₁'P₂') \ P₁'P₂'`
  (`Geometric.mem_rawSmoothVanishingSubfunctor_iff`). `emb` maps that boundary into
  `closure(P₁P₂) \ P₁P₂` (`map_mem_identityBoundary`), where `f` vanishes.
- `innerLevi_integralIntertwiner_formula`: the hypotheses are
  - `a : A → M`, a split component;
  - subgroups `V ⊂ G(F)` and `V' ⊂ N₂'(F)`, and a topological group isomorphism
    `e : V' ≃ₜ* V` with `e x = emb x`;
  - measures `haar'` on `V'` and `haar` on `V` with `haar = e_* haar'`;
  - a `P₁P₂`-regular `σ` (`IsPQRegular`);
  - intertwining operators `J : i_{P₁}^G(σ) → i_{P₂}^G(σ)` and
    `J' : i_{P₁'}^L(σ) → i_{P₂'}^L(σ)` satisfying `IsIntegralIntertwiner` for `(V, haar)`
    and `(V', haar')`;
  - `f ∈ i_{P₁}^G(σ)` and `F ∈ i_Q^G(i_{P₁'}^L(σ))` with
    `F(g)(x) = c(x)⁻¹ f(emb(x) g)` for all `g ∈ G(F)` and `x ∈ L(F)`.

  The conclusion is `J'(F(g))(x) = c(x)⁻¹ J(f)(emb(x) g)` for all `g` and `x`.

## Proof of the operator identity

1. Let `K = Ψ₁ ≫ i_Q^G(J') ≫ Ψ₂⁻¹ : i_{P₁}^G(σ) → i_{P₂}^G(σ)`. Then
   `K ≫ Ψ₂ = Ψ₁ ≫ i_Q^G(J')`. The formula for `Ψ₂` gives, for every `f₀`, `g` and `x`,
   `J'(Ψ₁(f₀)(g))(x) = c(x)⁻¹ K(f₀)(emb(x) g)`.
2. `c = 1` on `N₂'(F)`, hence on `V'` (`halfModulus_eq_one_of_mem_innerRadical`).
3. `K` satisfies `IsIntegralIntertwiner` for `(V, haar)`. Take `f₀ ∈ F̃^{<1̄}_{P₁P₂}(σ)` and
   a linear form `ℓ`, and put `φ = Ψ₁(f₀)(1) ∈ i_{P₁'}^L(σ)`. Then `φ(y) = c(y)⁻¹ f₀(emb y)`,
   so `φ ∈ F̃^{<1̄}_{P₁'P₂'}(σ)` by the first lemma. On `V'`, `c = 1` gives `φ(y) = f₀(e y)`.
   Integrability of `v ↦ ℓ(f₀(v))` for `e_* haar'` follows from that of `y ↦ ℓ(φ(y))` for
   `haar'` (`integrable_map_equiv`). For the integral, step 1 at `g = x = 1` with `c(1) = 1`
   gives `K(f₀)(1) = J'(φ)(1)`. Then
   `ℓ(K(f₀)(1)) = ℓ(J'(φ)(1)) = ∫_{V'} ℓ(φ(y)) dhaar' = ∫_V ℓ(f₀(v)) d(e_* haar')`
   (`integral_map_continuousMulEquiv`).
4. `J = K` by uniqueness of integral-normalized operators for regular `σ`
   (`integralIntertwiner_unique`).
5. `F = Ψ₁(f)`, because both have the same values `F(g)(x)` (`leviInductionStages_ext`).
   Step 1 with `f₀ = f` and `J = K` gives the conclusion.
