# The operator identity of Renard VII.3.5 (iii)

Lean module: `Langlands.Representation.Intertwining.PQOuterLeviOperator`.

This module proves the operator part of Renard VII.3.5 (iii) (Renard 2026, French version of
9 July 2026, printed pp.238–240 / PDF pp.244–246): for `P₁ = MN₁ ⊂ Q₁ = LU₁`,
`P₂ = MN₂ ⊂ Q₂ = LU₂` and `P' = MN'` a parabolic of `L` with
`P'(F) = P₁(F) ∩ L(F) = P₂(F) ∩ L(F)`, the integral-normalized operators
`J_{P₂|P₁}(σ)` and `J_{Q₂|Q₁}(i_{P'}^L(σ))` correspond under the induction-in-stages
isomorphisms `Φᵢ : i_{Pᵢ}^G(σ) ≅ i_{Qᵢ}^G(i_{P'}^L(σ))`. Renard proves this by computing
the integrals; the Lean proof below instead uses the uniqueness of an intertwining operator on
the `Q₁Q₂` side through its values on the boundary-vanishing subspace. The auxiliary lemmas
are internal.

## Declarations

### Haar measures on equal subgroups

For a nonarchimedean topological group `H` and subgroups `V`, `W` of `H` with Borel
measurable structures:

- `exists_haar_integral_eq_of_subgroup_eq`: if `V = W`, every Haar measure on `W` yields a Haar
  measure on `V` with `∫_W φ = ∫_V φ` for every `φ : H → ℂ` (push forward along the
  topological group isomorphism `W ≃ V`, `map_isHaarMeasure_integral_eq`).
- `integral_eq_of_subgroup_eq`: if moreover `H` is locally compact and second countable, `V`
  is closed, `V = W`, and Haar measures on `W` and `V` give the same integrals of continuous
  compactly supported functions `H → ℂ`, then they give the same integrals of every function
  `ψ : H → ℂ`. Proof: the Haar measure on `V` equals the pushforward of the one on `W`
  (`haar_eq_map_of_integral_eq`), and `integral_map_continuousMulEquiv` transports the
  integral.

### Isomorphisms of smooth representations

- `smoothRep_iso_inv_hom_apply`, `smoothRep_iso_hom_inv_apply`: for an isomorphism `e` of
  smooth representations, `e⁻¹ (e x) = x` and `e (e⁻¹ x) = x`.

### The outer Levi configuration

The section `Operator` takes the data and hypotheses of `PQIntertwiningOuterLeviStatement`
(without the opposites): connected reductive `G` over a nonarchimedean local field with
`G(F)` (canonical topology) locally compact and nonarchimedean; represented parabolics
`P₁ = MN₁`, `P₂ = MN₂`, `Q₁ = LU₁`, `Q₂ = LU₂` of `G` and `P' = MN'` of `L`, with
`l₂ ≫ p₂ = l₁ ≫ p₁`, `lQ₂ ≫ q₂ = lQ₁ ≫ q₁`, `P₁(F) ⊂ Q₁(F)`, `P₂(F) ⊂ Q₂(F)`,
`l' ≫ p' ≫ lQ₁ ≫ q₁ = l₁ ≫ p₁`, and `P'(F) = P₁(F) ∩ L(F) = P₂(F) ∩ L(F)` (with `L`
embedded through `Q₁`).

- `outer_levi₂_eq`: `l' ≫ p' ≫ lQ₂ ≫ q₂ = l₂ ≫ p₂`, i.e. `M` embedded through
  `P' ⊂ L ⊂ Q₂` is `M` embedded through `P₂`.
- `outer_parabolic₂_eq`: `P'(F) = L(F) ∩ P₂(F)` with `L` embedded through `Q₂`.

These are the hypotheses of the stage isomorphism `Φ₂ = leviInductionStagesIso` for
`P₂ ⊂ Q₂`; `Φ₁` uses the stated hypotheses for `P₁ ⊂ Q₁`.

- `outer_intertwiner_stages`: let `A_L → L` be a split component of `L`, `V`, `W` subgroups of
  `G(F)` with `V = W` and `V` closed, and Haar measures on `W` and `V` with the same integrals
  of continuous compactly supported functions on `G(F)`. For every smooth complex
  representation `σ` of `M(F)` such that `X = i_{P'}^L(σ)` is `Q₁Q₂`-regular with respect to
  `A_L` (`IsPQRegular`), every intertwining operator
  `J : i_{P₁}^G(σ) → i_{P₂}^G(σ)` given by the integral over `V` (`IsIntegralIntertwiner`) and
  every intertwining operator `J_Q : i_{Q₁}^G(X) → i_{Q₂}^G(X)` given by the integral over `W`,
  one has `J_Q (Φ₁ f) = Φ₂ (J f)` for all `f ∈ i_{P₁}^G(σ)`.

## Proof of `outer_intertwiner_stages`

Write `ev_g` for evaluation of an induced function at `g ∈ G(F)` and `ev^L_y` for evaluation
of an element of `X` at `y ∈ L(F)`. The stage formula (`leviInductionStagesIso_eval'`) gives

- `ev^L_1 (ev_g (Φ₁ f)) = ev_g f` and `ev^L_1 (ev_g (Φ₂ h)) = ev_g h`;
- `ev^L_y (ev_g (Φ₂ h)) = c_y · ev_{e(y) g} h` for a scalar `c_y` (the inverse half modulus of
  `U₂` at `y`), where `e : L(F) → G(F)` is the embedding through `Q₂`.

Set `T = Φ₂ ∘ J ∘ Φ₁⁻¹ : i_{Q₁}^G(X) → i_{Q₂}^G(X)`, so that `T (Φ₁ f) = Φ₂ (J f)`. It
suffices to prove `J_Q = T`. By the uniqueness lemma `intertwiner_eq_of_eval_one_eq`
(regularity of `X`), it suffices that `ev_1 (J_Q F) = ev_1 (T F)` for every `F` in the
boundary-vanishing subspace `S_Q` of `i_{Q₁}^G(X)` (functions vanishing on the boundary of the
open double coset `Q₁(F)Q₂(F)`).

1. *Reduction to `ev^L_1`.* For `H = Φ₂ h`, the formulas above give
   `ev^L_y (ev_1 H) = c_y · ev_{e(y)} h = c_y · ev_1 (ρ(e(y)) h) = c_y · ev^L_1 (ev_1 (ρ(e(y)) H))`,
   using that `Φ₂` intertwines and induced representations act by right translation; since
   `Φ₂` is surjective this holds for all `H`. As `J_Q` and `T` intertwine and `S_Q` is stable
   under `Q₂(F) ∋ e(y)`, it suffices to show `ev^L_1 (ev_1 (J_Q F)) = ev^L_1 (ev_1 (T F))` for
   `F ∈ S_Q`.
2. *Boundary vanishing transfers.* Write `F = Φ₁ f`. For `g` in the boundary of `P₁(F)P₂(F)`,
   `g` lies in the boundary of `Q₁(F)Q₂(F)` (`outer_boundary_subset`), so `ev_g F = 0` and
   `ev_g f = ev^L_1 (ev_g F) = 0`: `f` lies in the boundary-vanishing subspace of
   `i_{P₁}^G(σ)`.
3. *Integrals.* Then `ev^L_1 (ev_1 (T F)) = ev_1 (J f)`. Test both sides with an arbitrary
   linear functional `ℓ` on `σ` (a vector is zero when all functionals vanish on it), and put
   `ℓ' = ℓ ∘ ev^L_1` on `X`. By the integral formula for `J_Q` with `ℓ'`, the identity
   `ev^L_1 (ev_x (Φ₁ f)) = ev_x f`, `integral_eq_of_subgroup_eq`, and the integral formula for
   `J` with `ℓ`:
   `ℓ (ev^L_1 (ev_1 (J_Q F))) = ∫_W ℓ (ev_x f) dx = ∫_V ℓ (ev_x f) dx = ℓ (ev_1 (J f))`.
