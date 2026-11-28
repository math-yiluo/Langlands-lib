# Kummer algebras from unit eigenvectors

The module `Langlands.AlgebraicGeometry.FiniteEtale.KummerCyclicAlgebra`
turns an eigenvector of an algebra endomorphism into an equivariant map out
of a Kummer algebra, and normalizes a unit eigenvector over `R[1/t]` so that
the Kummer parameter is `1` or `t`. Declarations are in the namespace
`Langlands.AlgebraicGeometry.FiniteEtale`. The lift uses `A` and `B` in
one universe `u`, and the normalization uses `R` and `B` in one universe `u`.

## The lift `X ↦ v`

Let `B` be an `A`-algebra.

- `kummerLift a m v hv`, for `v ∈ B` with `v^m = a` (in `B`), is the
  `A`-algebra map `A[X]/(X^m - a) → B` sending `X` to `v`
  (Mathlib's `AdjoinRoot.liftAlgHom`); `kummerLift_root` records `X ↦ v`.
- `comp_kummerLift`: for a ring `R` with `[Algebra R A]`, an `A`-algebra
  endomorphism `σ` of `B` and `ζ ∈ rootsOfUnity m R` with `σ(v) = ζ v`, one
  has `σ ∘ kummerLift = kummerLift ∘ kummerScale R a m ζ`, where
  `kummerScale` (from `KummerCovers`) is `X ↦ ζX`. Both sides are
  `A`-algebra maps out of `AdjoinRoot` agreeing on the root
  (`AdjoinRoot.algHom_ext`).

## Normalization over `R[1/t]`

`exists_kummerLift_of_unit_eigenvector` assumes that `R` is a strictly
Henselian local domain (`HenselianLocalRing R`, `IsSepClosed (ResidueField R)`),
`t` is a prime element, `ℓ` is a prime invertible in `R`, `B` is an
`R[1/t]`-algebra (`A = Localization.Away t`) with an `A`-algebra endomorphism
`σ`, `ζ ≠ 1` is an `ℓ`-th root of unity of `R`, `v` is a unit of `B` with
`σ(v) = ζ v`, and `v^ℓ = w` for a unit `w` of `A`. It concludes that for
`a = 1` or `a = t` (in `A`) there are an `ℓ`-th root of unity `η ≠ 1` and an
`A`-algebra map `ψ : A[X]/(X^ℓ - a) → B` with `σ ∘ ψ = ψ ∘ (X ↦ ηX)`.

Proof as implemented:

1. By `StrictlyHenselianKummerUnits.exists_eq_unit_mul_zpow`, `w = u t^k`
   with `u ∈ Rˣ` and `k ∈ ℤ`. By `exists_pow_eq_of_isUnit`, `u = u₀^ℓ` with
   `u₀ ∈ Rˣ`. Write `k = ℓ q + k₀` with `0 ≤ k₀ < ℓ`.
2. Put `v₁ = v / (u₀ t^q)`. Since `σ` fixes the image of `A`, still
   `σ(v₁) = ζ v₁`, and `v₁^ℓ = t^(k₀)`.
3. If `k₀ = 0`, then `v₁^ℓ = 1` and `ψ = kummerLift 1 ℓ v₁`, `η = ζ` work.
4. Otherwise `k₀` is prime to `ℓ`; choose `k₁` with `k₀ k₁ = ℓ s + 1`. Put
   `v₂ = v₁^(k₁) / t^s`; then `v₂^ℓ = t` and `σ(v₂) = ζ^(k₁) v₂`. The root of
   unity `η = ζ^(k₁)` is not `1`: `ζ` has order `ℓ` (`orderOf_eq_prime`), and
   `ℓ ∣ k₁` would give `ℓ ∣ ℓ s + 1`. Take `ψ = kummerLift t ℓ v₂`.

## Provenance

This is the classical normalization in Kummer theory of an `ℓ`-th root
`v^ℓ = u t^k` of a unit of `R[1/t] = R[t⁻¹]` (for a unit `u` of a strictly
Henselian ring, which is an `ℓ`-th power), as in the description of cyclic
tame covers through roots of the equation `t` of the divisor (SGA 7 I,
Exposé I, 0.3–0.4; Stacks, *Fundamental Groups of Schemes*, Lemma 58.31.5,
Tag 0EYG). The formulation is internal to the Library.
