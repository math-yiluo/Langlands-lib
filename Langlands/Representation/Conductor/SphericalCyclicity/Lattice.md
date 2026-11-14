# Translates of extensions by zero

Author: Worker 392.

This helper module of the proof of
`Langlands.Conductor.OrderedUnramifiedSphericalCyclicityStatement` (see
[`OrderedUnramifiedSphericalCyclicity`](../OrderedUnramifiedSphericalCyclicity.md))
shows the following. For `h ∈ GL_(n+1)(F)`, the extension by zero of the translate
`ρ'(h) ψ` is a scalar multiple of a finite sum of right translates of the extension of
`ψ`. Hence the preimage of a subrepresentation under `extend`
([`Extension`](Extension.md)) is a subrepresentation. The definitions are internal
auxiliary constructions, with no literature source. All declarations are in
`Langlands.Conductor.SphericalCyclicity`.

## The lattice of small vectors

- `smallSubgroup m` is the additive subgroup of `Fin m → F` of vectors all of whose
  coordinates have valuation `< 1`. `mem_smallSubgroup` says membership is
  `IsSmall`.
- `exists_pow_mul_le_one`, `val_pow_mul_antitone` and `exists_pow_mul_integral`:
  for every matrix `A` there is `N` with `ϖ^N A` integral. The proof writes
  `v x = (v ϖ)^k` (uniformizing hypothesis) and takes a maximum over the entries.
- Topology, for a nonarchimedean local field: `ball_eq_preimage` writes
  `{x | v x < 1}` as the preimage of `𝒪` under `x ↦ ϖ⁻¹ x`. So it is open
  (`isOpen_ball_one`, by `Valuation.isOpen_integer`). It equals the closed ball
  `{x | v x ≤ v ϖ}`, which is compact (`isCompact_ball_one`, by
  `IsNonarchimedeanLocalField.isCompact_closedBall`). `coe_smallSubgroup`,
  `isOpen_smallSubgroup` and `isCompact_smallSubgroup` give the same for the product.
- `preSmall A` is the subgroup of `u` with `A u` small (`mem_preSmall`). It is open
  (`isOpen_preSmall`), by continuity of `mulVec`. `preSmallIn A` is the same subgroup
  inside `smallSubgroup m` (`mem_preSmallIn`).
- `finite_quotient_preSmallIn`: the quotient `smallSubgroup m ⧸ preSmallIn A` is
  finite. This is `AddSubgroup.quotient_finite_of_isOpen`, applied to an open subgroup
  of a compact group.

## Sums of cell functions

- `cellFun_sum`: suppose finitely many conditions `P i` each imply `P0`, and every
  `v` with `P0 v` satisfies exactly one `P i`. Then
  `Σ_i cellFun (P i) φ = cellFun P0 φ`. The proof uses `Finset.sum_eq_single`.
- `preSmall_le_smallSubgroup`: if `ϖ^N h` is integral and `α = ϖ^(-N)`, then
  `preSmall (α • h⁻¹) ⊆ smallSubgroup`. Indeed `u = (ϖ^N h)(α h⁻¹ u)` and
  `mulVec_val_lt_one` applies.
- `evalAt hq z x` is evaluation at `x`, as a linear functional. `value_sum` says that
  evaluation commutes with finite sums.

## Translates

Fix `hq` and `z : Fin (n + 2) → ℂˣ`, and write `ρ` and `ρ'` for the Library's
`principalSeries` of ranks `n + 2` and `n + 1`.

- `extFun_mul_translate`: with `cu = z_0^(ord α) s^(-(n+1) ord α + ordDet h)`,

  ```
  extFun ψ (x L(y) diag(α, h)) =
    cu · cellFun (v ↦ IsSmall (α • h⁻¹ (v + y))) (value (ρ'(h) ψ)) x.
  ```

  This is `cellFun_mul_blockDiag` followed by `cellFun_mul_lowerUnip`.
- `exists_extend_translate_eq`: for every `ψ` and `h` there are a finite type `ι`,
  elements `g : ι → GL_(n+2)(F)` and `c : ℂ` such that
  `extend (ρ'(h) ψ) = c • Σ_i ρ(g i) (extend ψ)`.

  Proof: choose `N` with `ϖ^N h` integral and put `α = ϖ^(-N)` and `A = α • h⁻¹`.
  Let `ι` be the finite quotient `smallSubgroup ⧸ preSmallIn A`, with representatives
  `y ξ`, and put `g ξ = L(y ξ) diag(α, h)` and `c = cu⁻¹`. By
  `extFun_mul_translate`, the right side at `x` is the sum over `ξ` of the cell
  functions with conditions `P_ξ(v) : A (v + y ξ)` small. Every `P_ξ` implies that `v`
  is small, because `preSmall A ⊆ smallSubgroup` and `y ξ` is small. Each small `v`
  satisfies `P_ξ` for exactly one `ξ`, namely the class of `-v`, since the `y ξ` are
  representatives modulo `preSmall A`. So `cellFun_sum` turns the sum into
  `cellFun IsSmall (value (ρ'(h) ψ)) = extFun (ρ'(h) ψ)`.
- `extend_translate_mem`: if `extend ψ ∈ S` for a subrepresentation `S`, then
  `extend (ρ'(h) ψ) ∈ S`.
- `pullback hϖ hq z S` is the subrepresentation of `ρ'` with underlying submodule
  `S.comap extend`. It is stable by `extend_translate_mem`.
- `mem_pullback`: `ψ ∈ pullback S ↔ extend ψ ∈ S` (by `Iff.rfl`).
