# Injectivity of the truncated Taylor map along a smooth section

This module is part of the proof of
`Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement` (Stacks Project, Tag 05FT).
It proves that the map `theta σ t k` of `Langlands.CommutativeAlgebra.IntegralFibre.Taylor` is
injective when the section lands in a formally smooth localization.

## Definitions

Let `S` be an `A`-algebra with section `σ`. Let `δ : S →ₗ[A] (Fin d → A)` be a derivation at
`σ`, meaning `δ (x * y) = σ x • δ y + σ y • δ x`.

- `TPoly A d k`: the ring `A[T₁,…,T_d]/(T)^k`.
- `firstOrderPoly σ δ s = C (σ s) + ∑ i, C (δ s i) * X i`.
- `firstOrder σ δ hδ : S →ₐ[A] TPoly A d 2`: the class of `firstOrderPoly`, an algebra
  homomorphism.
- `taylorLift σ δ hδ h hh K hK : S →ₐ[A] TPoly A d K`, for `2 ≤ K`: a lift of `firstOrder` through
  `TPoly A d K → TPoly A d 2`. It exists when `h : S` has `IsUnit (σ h)` and
  `Localization.Away h` is formally smooth over `A`.

## Statements

- `delta_one`, `firstOrderPoly_mul_sub_mem`: `δ 1 = 0`, and `firstOrderPoly` is multiplicative
  modulo `(X)^2`.
- `firstOrder_apply`: the formula for `firstOrder`.
- `mk_idealOfVars_pow_eq_bot`, `factor_ker_isNilpotent`: the kernel of
  `TPoly A d K → TPoly A d 2` is nilpotent.
- `firstOrder_isUnit_powers`: `firstOrder` sends powers of `h` to units, since `firstOrder h` is
  the unit `C (σ h)` plus a nilpotent.
- `factor_taylorLift`: `taylorLift` reduces to `firstOrder` modulo `(X)^2`.
- `theta_injective_of_formallySmooth`: assume `σ (t i) = 0` and `δ (t i) = Pi.single i 1` for all
  `i`, `IsUnit (σ h)`, and `Algebra.FormallySmooth A (Localization.Away h)`. Then `theta σ t k` is
  injective for every `k`.

## Proofs

`firstOrder` extends to `Localization.Away h` by `IsLocalization.liftAlgHom`. Formal smoothness
(`Algebra.FormallySmooth.liftOfSurjective`, using the nilpotent kernel) lifts it to
`A[T]/(T)^(k+2)`. Reducing modulo `(T)^k` gives a map `ψ` on `S`. Elements of `J` map into the
image of `(X)`, so `ψ` kills `J^k` and factors through `S ⧸ J^k`. Each `ψ (t i)` lifts to some
`q i` with `q i - X i ∈ (X)^2`, because `firstOrder (t i) = X i`. The criterion
`theta_injective_of_lift` then applies.

## Provenance

This is internal to the 05FT proof, written by Worker 281. It is the standard computation of the
completion along a section of a smooth morphism as a power series ring; see Stacks Remark 05FU.
