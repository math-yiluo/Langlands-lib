# Connectedness of Greenberg groups

This file proves that the Greenberg group of a smooth affine `Z` with geometrically
connected fibres is geometrically connected, when the residue field `k` is algebraically
closed (the connectedness clause of KP Theorem A.4.19). The Lean route is an
idempotent-constancy argument, not the fibration argument of the literature.

General lemmas:
- `eq_zero_or_one_of_connectedSpace`: in a ring with connected spectrum, every idempotent
  is `0` or `1`. `basicOpen e` is clopen, hence empty or everything. In either case `e` or
  `1 - e` is nilpotent and idempotent, so it vanishes.
- `connectedSpace_of_idempotents`: the converse, for a nontrivial ring. This uses
  `PrimeSpectrum.isClopen_iff`.
- `isNilpotent_of_forall_algHom`: over an algebraically closed field, an element of
  `K[σ] ⧸ I` (`σ` finite) killed by every `K`-point is nilpotent. This is the Mathlib
  Nullstellensatz `vanishingIdeal_zeroLocus_eq_radical`.
- `isNilpotent_ker_of_injective`: kernels that embed into a nilpotent ideal are
  nilpotent.

Paths (`GreenbergRingScheme.*`):
- `pairAlg`: the pairs `(a, a')` in `ℛ(k)²` with `red a = red a'`.
- `constAlg`: the points of `ℛ(k[t])` whose reduction is constant.
- `endpoints : constAlg → pairAlg`, `x ↦ (x(0), x(1))`. It is surjective by linear
  interpolation of coordinates `(1 - t)·a + t·a'`, using linearity of `red` in the
  coordinates. Its kernel lies in `ker red`, so it is nilpotent.
- `idempotent_eq_of_red_eq`: if two `k`-points `ψ, ψ'` of `repAlg` classify points of `O`
  with the same reduction, the pair lifts (formal smoothness of `O`) to a `k[t]`-point
  `χ` with `χ(0) = ψ`, `χ(1) = ψ'`. For an idempotent `e`, `χ(e)` is an idempotent of
  `k[t]`, hence constant, so `ψ(e) = ψ'(e)`.

Fibre (`idempotent_const`): let `D = k ⊗_R O` have only trivial idempotents. Lift the
canonical `O → D` through `red_D : ℛ(D) → D`, which is surjective with nilpotent kernel,
to `Γ : O → ℛ(D)`, classified by `χ : repAlg → D`. For each `k`-point `ψ` with reduction
`r : O → k`, the point `y = id ⊗ r : D → k` gives `χ ≫ y` with the same reduction as `ψ`.
Hence `ψ(e) = y(χ(e))`, and `χ(e) ∈ {0, 1}`. So `e` is constantly `0` or constantly `1` on
`k`-points.

Main:
- `tensor_idempotent`: for `Z` geometrically connected, `K ⊗_R O(Z)` has only trivial
  idempotents for every field `K` over `R`. Geometric connectedness transfers to
  `Spec O(Z) → Spec R` along `coordinateIso`, and the fibre over `Spec K` is
  `Spec (O(Z) ⊗_R K)` (`pullbackSpecIso`).
- `connectedSpace_greenbergGroup`: `repAlg` is nontrivial, since it has the `k`-point
  coming from the unit section. By constancy and the Nullstellensatz, every idempotent `e`
  satisfies `e = 0` or `1 - e = 0`.
- `geometricallyConnected_greenbergGroup`: from connectedness by the Library theorem
  `GroupScheme.geometricallyConnected_of_connected`, for smooth groups over a field.
