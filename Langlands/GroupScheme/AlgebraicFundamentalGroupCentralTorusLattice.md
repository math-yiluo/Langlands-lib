# Exactness of induced maps on quotient lattices

Author: Worker 149 (Task 6713). This is a helper module for the proof of
`Langlands.GroupScheme.AlgebraicFundamentalGroup.CentralTorusFundamentalExactnessStatement`
in `Langlands.GroupScheme.AlgebraicFundamentalGroupCentralTorusProof`. It contains
the two pure linear-algebra steps of that proof. It imports only
`Mathlib.LinearAlgebra.Quotient.Basic`.

## Statements

Names are in `Langlands.GroupScheme.AlgebraicFundamentalGroup`. `R` is a commutative
ring and all other types are `R`-modules.

- `quotient_exact_of_lattice_exact RA RB RC α β ρB ρC σ hRB hRC hα hαβ hβ hσ hσρ hρC m₁ m₂ hm₁ hm₂`.
  Let `RA ≤ A`, `RB ≤ B` and `RC ≤ C` be submodules, and let `α : A → B` and
  `β : B → C` be linear with `α` injective, `ker β = range α` and `β` surjective.
  Let `ρB : SB → B` and `ρC : SC → C` be linear with `RB = range ρB`,
  `RC = range ρC` and `ρC` injective. Let `σ : SB → SC` be a linear bijection with
  `ρC (σ s) = β (ρB s)` for all `s`. Let `m₁ : A ⧸ RA → B ⧸ RB` and
  `m₂ : B ⧸ RB → C ⧸ RC` be linear maps with `m₁ [ν] = [α ν]` and `m₂ [x] = [β x]`
  on representatives. Then `m₁` is injective, `m₂` is surjective and
  `range m₁ = ker m₂`.

  `RA` is arbitrary here. The hypotheses only require `m₁` to be some linear map
  with the stated values on representatives, so the lemma does not itself
  assert that `α` maps `RA` into `RB`. Such a map exists only in that case.

- `exact_of_comparison F₁ F₂ m₁ m₂ κB κC hκB hκC h₁ h₂ hm`. Let
  `F₁ : A → B`, `F₂ : B → C`, `m₁ : A → B'` and `m₂ : B' → C'` be linear, and let
  `κB : B → B'` be a linear bijection and `κC : C → C'` an injective linear map with
  `κB ∘ F₁ = m₁` and `κC ∘ F₂ = m₂ ∘ κB`. If `m₁` is injective, `m₂` is surjective
  and `range m₁ = ker m₂`, then `F₁` is injective, `F₂` is surjective and
  `range F₁ = ker F₂`.

## Provenance

These are internal lemmas with no literature counterpart. The first lemma is the
lattice argument in the proof of Kaletha–Prasad (2023), Lemma 11.5.1 (printed p. 430,
PDF p. 461): an exact cocharacter sequence with compatible coroot lattices gives an
exact sequence of quotients. The second moves exactness from one choice of
presentations to another along comparison maps.

## Proofs

- `quotient_exact_of_lattice_exact`. First, `β ∘ α = 0` because `ker β = range α`.
  - Injectivity of `m₁`: if `[α ν] = 0`, then `α ν = ρB s` for some `s`. Then
    `ρC (σ s) = β (α ν) = 0`, so `σ s = 0` by injectivity of `ρC`, so `s = 0`, so
    `α ν = 0` and `ν = 0`.
  - Surjectivity of `m₂`: lift a class to `C`, lift that element through `β`, and
    apply `hm₂`.
  - `range m₁ ⊆ ker m₂` because `β ∘ α = 0`.
  - `ker m₂ ⊆ range m₁`: if `β x = ρC t`, write `t = σ s` by surjectivity of `σ`. Then
    `x - ρB s ∈ ker β = range α`, so `x - ρB s = α ν`, and `[x] = m₁ [ν]` because
    `ρB s ∈ RB`.
- `exact_of_comparison` is a diagram chase. Injectivity and the two inclusions follow
  from the commuting squares, injectivity of `κC` and bijectivity of `κB`. Surjectivity
  of `F₂` lifts `κC y` through `m₂`, pulls the lift back through `κB`, and uses
  injectivity of `κC`.
