# Invariant complements for representations of compact groups

Module `Langlands.Representation.CompactMaschke`, namespace `Langlands.CompactMaschke`.
Worker 174 wrote it as a step towards
`Langlands.Automorphic.CuspidalArchimedeanIrreducibleAdmissibleComponentStatement` (G1, Task 5992).
Provenance: the standard averaging proof of complete reducibility of finite-dimensional
continuous representations of compact groups (Weyl's unitary trick in the form of an averaged
projection). It is internal infrastructure; Mathlib's `Maschke` covers finite groups only.

Throughout, `K` is a compact topological group.

- `continuous_apply_of_continuous`: on a finite-dimensional normed space, if every orbit map
  `k ↦ ρ k y` is continuous, then `x ↦ ρ (g x) (z x)` is continuous for continuous `g`, `z`.
  Write `z x` in a basis: `ρ (g x) (z x) = ∑ⱼ cⱼ(z x) ρ (g x) (bⱼ)`.
- `exists_isCompl_invariant` (**Maschke for compact groups**): let `E` be a
  finite-dimensional complex normed space with a representation `ρ` with continuous orbit
  maps. Then every `K`-stable subspace `U` has a `K`-stable complement. Proof:
  1. Take the Borel structure and the Haar measure `μ` normalized by `μ(K) = 1`
     (`haarMeasure ⊤`, `haarMeasure_self`).
  2. Let `p₀` be a linear projection onto `U` along any complement, and put
     `P y = ∫ ρ k (p₀ (ρ k⁻¹ y)) dμ(k)`. The integrand is continuous on a compact space,
     hence integrable.
  3. `P` takes values in `U`: `id - p₀` kills every value of the integrand and commutes with
     the integral.
  4. `P` fixes `U`, since the integrand is constant there.
  5. `P` is equivariant, by left invariance of `μ` (`integral_mul_left_eq_self`) and
     `ContinuousLinearMap.integral_comp_comm`.
  6. The kernel of `P` is a `K`-stable complement of `U` (`LinearMap.isCompl_of_proj`).
- `exists_isCompl_invariant_of_weak`: the same for a finite-dimensional complex vector space
  without a norm. The hypothesis is that `k ↦ μ (ρ k y)` is continuous for every linear form
  `μ`, as in the Library's `(𝔤, K)`-module predicates. Put the norm induced by a basis
  (`NormedAddCommGroup.induced`, `NormedSpace.induced`). Then orbit maps are continuous,
  because their coordinates are.
- `exists_lift_intertwiner` (**lifting intertwiners**). Hypotheses:
  - `κ` is a representation on `N` whose vectors lie in finite-dimensional stable
    subspaces, with weakly continuous orbit maps;
  - `q : N → N''` is equivariant;
  - `ψ` is an intertwiner from a matrix representation `τ` into `N''` with values in the
    range of `q`.

  Then `ψ = q ∘ ψ'` for an intertwiner `ψ'` into `N`. Proof:
  1. Lift `ψ` of the standard basis vectors.
  2. Take a finite-dimensional stable `E` containing the lifts (a finite supremum).
  3. Choose a stable complement `U'` of `ker q ∩ E` in `E` by the previous theorem. `q` is
     injective on `U'` with the same image as `E`.
  4. Put `ψ' = (q|_{U'})⁻¹ ∘ ψ`. Both sides of the equivariance identity lie in `U'`, where
     `q` is injective.
