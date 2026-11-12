# Forms whose coefficients factor through a quotient of the level

Author: Worker 19.

This module gives a general algebraic form of Harris's isomorphism (4.8).
A level `K` has two components, `fst : K →* A` and `snd : K →* B`, and an
embedding `inr : B →* K` of the second one. The smaller level `K'` is the
set of `k` with `snd k` in a subgroup `H` of `B`. Suppose every stabilizer
of a double coset modulo `K` has trivial components. Then a form of level
`K'` whose coefficients factor through `fst` is determined freely by its
values at the points `x.out · (inr b)⁻¹`. Here `x` runs over the double
cosets modulo `K` and `b` over `B`, and the value depends only on the coset
`b H`. So the forms of level `K'` are the functions
`B ⧸ H → (ι Γ \ G / K → V)`, and hence the `R`-linear maps
`R[(B ⧸ H) × ι Γ \ G / K] → V`.

In Harris's case `K = K^{ℓ,p} × K_ℓ × C_p`, `K' = K^{ℓ,p} × K_ℓ × H_p`,
`A = K_ℓ`, `B = C_p` and `H = H_p`. The companion module
`Langlands.Shimura.Unitary.HarrisInvariantForms` makes this specialization.

## Source

Harris (1999), Section 4, printed p. 311 (PDF p. 13): "The right-hand side
of (4.7) is the sum of `M` copies of the group `D_m(K_{ℓ,m} × C_p/H_p)` of
`𝒪_m`-valued functions on `K_{ℓ,m} × C_p/H_p`. Via the duality between
functions and group rings, this is canonically isomorphic to
`Hom(𝒪_m[K_{ℓ,m} × C_p/H_p]^M, 𝒪_m)`, and thus the decomposition (4.6)
yields a canonical isomorphism
(4.8) `𝒜_ℓ(GJ, 𝓛_m, H(m))^{K_ℓ} ⥲ Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`."

The module does not quote a general statement from the literature. The
general formulation is written for this module (see Provenance).

## Setting

All declarations are in namespace `Langlands.Shimura.EquivariantForms`.

- `R` is a commutative ring, `ι : Γ →* G` a group homomorphism, and
  `K' ≤ K` subgroups of `G`. `A` and `B` are groups and `H` is a subgroup of
  `B`.
- `V` is an `R`-module and `ρ : Representation R A V`.
- `forms ι K' σ` is the published module of forms of level `K'`: functions
  `f : G → V` with `f (ι γ * g) = f g` and `f (g * k) = σ k⁻¹ (f g)` for
  `k ∈ K'`.
- `DoubleCosets ι K` is the published double coset space `ι Γ \ G / K`.
  `x.out` is a chosen representative of a double coset `x`. The published
  `outFactor ι K g` is an element `k` of `K` with `g = ι γ * x.out * k`,
  where `x` is the double coset of `g`
  (`exists_eq_mul_out_mul_outFactor`).
- `doubleCosetStabilizer ι K g` is the published stabilizer `Δ_g`: the
  `k ∈ K` with `ι γ * g = g * k` for some `γ`.

## Declarations

### Level factorizations

- `LevelFactorization K K' A B H` is a structure with fields:
  - `le : K' ≤ K`;
  - `fst : K →* A`, `snd : K →* B` and `inr : B →* K`;
  - `fst_inr : fst (inr b) = 1` and `snd_inr : snd (inr b) = b`;
  - `mem_iff : (k : G) ∈ K' ↔ snd k ∈ H` for `k : K`.
- `mem_of_snd_eq_one`: if `snd k = 1` then `k ∈ K'`.
- `inr_mem`: `inr b ∈ K'` for `b ∈ H`.
- `normal`: if `H` is normal in `B`, then `K'` is normal in `K`.
- `rep c ρ` (an abbreviation) is the representation `k' ↦ ρ (fst k')` of
  `K'`.

### Values of forms

Let `c` be a level factorization and `f` a form of level `K'` with
coefficients `rep c ρ`.

- `forms_apply_mul_of_mem`: `f (g k) = ρ (fst k)⁻¹ (f g)` for `k ∈ K'`.
- `forms_apply_mul`: `f (g k) = ρ (fst k)⁻¹ (f (g · inr (snd k)))` for every
  `k ∈ K`.
  - Proof: `(inr (snd k))⁻¹ k` has trivial `B`-component, so it lies in `K'`.
- `forms_apply_mul_inr_mul`: `f (g · inr (b h)) = f (g · inr b)` for
  `h ∈ H`.
- `forms_apply_mul_inr_inv` (for `H` normal):
  `f (y · (inr a)⁻¹) = f (y · (inr b)⁻¹)` when `a⁻¹ b ∈ H`. It uses
  `b a⁻¹ ∈ H`, which follows from normality.

### The isomorphism

Assume `H` is normal in `B`.

- `factorRestrict c f : B ⧸ H → DoubleCosets ι K → V` sends `[b]` and `x` to
  `f (x.out · (inr b)⁻¹)` (`factorRestrict_mk`). It is well defined by
  `forms_apply_mul_inr_inv`.
- `factorLift c ρ φ : G → V`, for `φ : B ⧸ H → DoubleCosets ι K → V`, sends
  `g` to `ρ (fst k)⁻¹ (φ [(snd k)⁻¹] x)`. Here `x` is the double coset of
  `g` and `k = outFactor ι K g`.

The remaining results assume the stabilizer hypothesis
`hΔ : ∀ g, doubleCosetStabilizer ι K g ≤ ker fst ⊓ ker snd`.

- `factorLift_eq`: for every decomposition `g = ι γ · x.out · k` with
  `k ∈ K`, `factorLift c ρ φ g = ρ (fst k)⁻¹ (φ [(snd k)⁻¹] x)`.
  - Proof: two such decompositions differ by an element `k₁ k₂⁻¹` of the
    stabilizer of `x.out`. By `hΔ` its components are trivial, so `fst` and
    `snd` agree on `k₁` and `k₂`.
- `factorLift_mem`: `factorLift c ρ φ` is a form of level `K'` with
  coefficients `rep c ρ`.
  - Proof: invariance under `ι Γ` follows from `factorLift_eq`. For `k₀` in
    `K'`, write `g k₀ = ι γ · x.out · (k k₀)`. The `B ⧸ H`-argument does not
    change, because `snd k₀ ∈ H` and `H` is normal. The `A`-argument picks
    up `ρ (fst k₀)⁻¹`.
- `factorLinearEquiv c hΔ` is the `R`-linear equivalence from the forms of
  level `K'` with coefficients `rep c ρ` to the functions
  `B ⧸ H → DoubleCosets ι K → V`. It is `factorRestrict`, with inverse
  `factorLift`.
  - `factorLinearEquiv_apply_mk`: the image of `f` takes the value
    `f (x.out · (inr b)⁻¹)` at `[b]` and `x`.
  - `factorLinearEquiv_symm_apply_coe`: the form attached to `φ` takes the
    value `ρ (fst k)⁻¹ (φ [(snd k)⁻¹] x)` at `ι γ · x.out · k`.
  - Proof of the two inverse laws: `forms_apply_mul` reduces a form to its
    values at the points `x.out · inr (snd k)`, and `factorLift_eq` with
    `k = (inr b)⁻¹` gives back `φ [b] x`.

Assume moreover that `K'` is normal in `K` (for instance by `normal`).

- `factorEquiv c hΔ` is `factorLinearEquiv` as an equivalence of
  representations of `K`. Its source is the published `levelAction` of `K`
  on the forms of level `K'`, `(k • f) g = ρ (fst k) (f (g k))`. Its target
  is the published `functionRepresentation` of `B` on
  `B ⧸ H → (DoubleCosets ι K → V)` with trivial action on the values,
  `(b • φ) q = φ (b⁻¹ q)`, restricted to `K` along `snd`
  (`factorEquiv_apply_mk`).
- `factorHomEquiv c hΔ` composes `factorEquiv` with the inverse of the
  published duality `permutationDualEquiv` between functions and group
  rings. Its target is the representation of `B` on
  `Hom_R(R[B ⧸ H], DoubleCosets ι K → V)` (the published `permutation`
  representation and `linHom`), restricted to `K` along `snd`.
  `factorHomEquiv_apply_single`: the linear map attached to `f` sends the
  basis vector of `[b]` to the function `x ↦ f (x.out · (inr b)⁻¹)`.
- `factorFinsuppEquiv c hΔ` (no normality of `K'` needed) is the `R`-linear
  equivalence from the forms of level `K'` to the `R`-linear maps
  `R[(B ⧸ H) × DoubleCosets ι K] → V`. It is `factorLinearEquiv` followed by
  uncurrying and Mathlib's `Finsupp.llift`.
  `factorFinsuppEquiv_apply_single`: the basis vector of `([b], x)` goes to
  `f (x.out · (inr b)⁻¹)`.

### Invariants

- `invariants_comp_eq`: let `τ` be a representation of a group `K`, `s` a
  homomorphism `A →* K` and `N` a subgroup of `K` on which `τ` is trivial.
  If every `k ∈ K` is `s a · n` with `n ∈ N`, then the invariants of `τ ∘ s`
  equal the invariants of `τ`.

## Scope

- **Not Harris's statement itself.** These are general algebraic results.
  `HarrisInvariantForms` specializes them to Harris's levels and states
  (4.8).
- **Number of copies.** The target uses all double cosets
  `ι Γ \ G / K`, not a finite number `M` of them. No finiteness is assumed
  or proved.
- **Stabilizer hypothesis.** `hΔ` is assumed, not proved. In Harris's case it
  follows from his hypothesis (4.5); see `HarrisInvariantForms`.

## Provenance

The motivation is Harris (1999), Section 4, printed p. 311, (4.7)-(4.8),
read in the original (rendered page). The general formulation through a
`LevelFactorization`, the stabilizer hypothesis `hΔ`, the explicit inverse
`factorLift`, and `invariants_comp_eq` are written for this module. They
extend Worker 61's published restriction to double cosets
(`levelDoubleCosetEquiv`) to coefficients that factor through `fst`.

Source ID and SHA-256 fingerprint:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Formal dependencies:

- the published `Langlands.Shimura.EquivariantFormsDoubleCoset`
  (`DoubleCosets`, `doubleCosetStabilizer`, `outFactor`,
  `exists_eq_mul_out_mul_outFactor`, `mul_inv_mem_doubleCosetStabilizer`),
  and through it `Langlands.Shimura.EquivariantForms` (`forms`,
  `levelAction`);
- the published `Langlands.Induction.functionRepresentation`,
  `Langlands.Induction.permutation` and
  `Langlands.Induction.permutationDualEquiv`
  (`Langlands.Representation.Induction`);
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0.

The Mathlib results used include `DoubleCoset.mk_mul_mem`,
`DoubleCoset.mk_mem_mul`, `DoubleCoset.out_eq'`, `QuotientGroup.eq`,
`QuotientGroup.leftRel_apply`, `LinearEquiv.curry`, `Finsupp.llift` and
`Representation.mem_invariants`.
