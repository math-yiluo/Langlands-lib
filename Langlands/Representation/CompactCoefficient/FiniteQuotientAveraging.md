# Averaging equivariant linear maps over a finite quotient

Author: Worker 1709. Module
`Langlands.Representation.CompactCoefficient.FiniteQuotientAveraging`, namespace
`Langlands.FiniteQuotientAveraging`.

This is an internal helper for the proof of Renard VI.3.6 (the Proposition
after the Lemma, printed p.148 / PDF p.154, source
`renard-2026-representations-groupes-reductifs-padiques`). It formalizes the
step "average `ḡ · s₀ = π(g) ∘ s₀ ∘ τ(g⁻¹)` over the finite group
`G / ⁰G Z(G)`". The Lean version needs no commutativity of the quotient and
works for any subgroup `N` with finitely many left cosets. The facts are
elementary and derived here; no further literature claim is made.

## Setting

`G` is a group (no topology), `ρ`, `σ`, `τ` are complex representations of `G`
on modules `V`, `W`, `U` in arbitrary universes, and `N : Subgroup G`.

## Definitions

- `conj ρ σ φ g := σ g ∘ₗ φ ∘ₗ ρ g⁻¹` for a linear map `φ : V →ₗ[ℂ] W`.
- `IsEquivariantOn ρ σ N φ`: `φ (ρ n v) = σ n (φ v)` for all `n ∈ N` and all `v`.
- `average ρ σ N φ`, given `[Fintype (G ⧸ N)]`: the linear map
  `(card (G ⧸ N))⁻¹ • ∑ q : G ⧸ N, conj ρ σ φ q.out`, using the representatives
  `Quotient.out`.
- `averageMap hφ`: `average ρ σ N φ` bundled as an intertwiner
  `ρ.IntertwiningMap σ`, for `hφ : IsEquivariantOn ρ σ N φ`.

## Results

- `conj_mul_of_mem`, `conj_eq_of_mk_eq`: for an `N`-equivariant `φ`, the
  conjugate `conj ρ σ φ g` depends only on the left coset `gN`.
- `conj_intertwiningMap`: conjugation fixes intertwiners.
- `conj_mul_apply`: `conj ρ σ φ (h * g) (ρ h v) = σ h (conj ρ σ φ g v)`.
- `average_isIntertwining`: if `φ` is `N`-equivariant, then
  `average ρ σ N φ (ρ h v) = σ h (average ρ σ N φ v)` for every `h : G`. The proof
  reindexes the sum by the permutation `q ↦ h • q` of `G ⧸ N`, then uses
  `(h • q).out N = h * q.out N` and the coset independence above.
- `average_intertwiningMap`: averaging an intertwiner returns it. Every term
  equals the intertwiner and the factor `(card (G ⧸ N))⁻¹` cancels the number of
  terms (nonzero since the quotient is nonempty).
- `average_comp_left`, `average_comp_right`: averaging commutes with
  composition by an intertwiner on the left or on the right.
- `isEquivariantOn_sup_center`: if the centre acts on both `V` and `W` by the
  same character `χ : center G →* ℂˣ` (`ρ z v = χ z • v`, `σ z w = χ z • w`),
  an `H`-equivariant map is `H ⊔ center G`-equivariant. An element of the join
  is `h z` with `h ∈ H` and `z` central (`Subgroup.mem_sup_of_normal_right`);
  `z` acts by the same scalar on both sides.
