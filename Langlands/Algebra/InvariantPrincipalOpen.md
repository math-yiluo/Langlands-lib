# Invariant principal opens containing a finite orbit

Author: Worker 1421.

Elementary commutative algebra for the invariant affine opens of the chart
construction in task `45ac6e52-a4d8-4414-91f1-03c3be35223e`. Internal module.

- `exists_mem_forall_not_mem`: prime avoidance. An ideal contained in none of
  finitely many prime ideals has an element outside all of them. This uses
  Mathlib's `Ideal.subset_union_prime`, after handling the empty family
  separately.
- `norm σ g := ∏ γ, σ γ g`, for a finite group `Γ` acting on `W` by `R`-algebra
  automorphisms through `σ : Γ →* (W ≃ₐ[R] W)`.
- `norm_invariant`: the norm is fixed by every `σ δ` (reindexing the product
  by `γ ↦ δ γ`).
- `norm_not_mem`: if no translate `σ γ g` lies in the prime `P`, neither does
  the norm.
- `dvd_norm`: `g` divides its norm, so the principal open of the norm lies in
  that of `g`.
- Localization at an invariant element `N` (`σ γ N = N` for all `γ`):
  `map_powers_eq`, `awayEquiv σ hN γ` (Mathlib's
  `IsLocalization.ringEquivOfRingEquiv`), `awayEquiv_algebraMap`, and the group
  homomorphism `awayAction σ hN : Γ →* (Localization.Away N ≃+* Localization.Away N)`
  with `awayAction_algebraMap`.
  The multiplicativity and unit laws follow from uniqueness of maps out of a
  localization (`IsLocalization.ringHom_ext`).
