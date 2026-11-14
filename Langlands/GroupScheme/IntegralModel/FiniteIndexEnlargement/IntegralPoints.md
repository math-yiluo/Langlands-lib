# Integral points detect divisibility on smooth algebras

Worker 33, task `e1575004-9fac-4821-9bc9-ddcb15e7cbf3` (Task 6018). This is an internal helper
module for the proof of
`Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementStatement` (KP Proposition A.7.1,
finite-index part). It introduces no definitions and no external statements. It proves only
the theorems below, from Mathlib and two published Library results.

## Rational points of reduced algebras

`exists_algHom_ne_zero`: let `k` be an algebraically closed field and `T` a reduced `k`-algebra
of finite type. A nonzero `t : T` is nonzero at some `k`-algebra map `T →ₐ[k] k`.

Proof: `T` is a Jacobson ring, and its zero ideal is radical because `T` is reduced. So the
Jacobson radical of `⊥` is `⊥`, and some maximal ideal `J` does not contain `t`. The field
`T ⧸ J` is finite over `k` (Jacobson property), so it is integral over `k`. Since `k` is
algebraically closed, `k → T ⧸ J` is bijective. Composing the quotient map with the inverse of
this isomorphism gives the required point.

## Henselian local rings with algebraically closed residue field

Let `R` be a Henselian local ring with algebraically closed residue field `k`, and let `A` be a
smooth `R`-algebra in the same universe.

`mem_map_maximalIdeal_of_forall` (key lemma): suppose `a : A` satisfies `σ a ∈ 𝔪_R` for every
`R`-algebra map `σ : A →ₐ[R] R`. Then `a` lies in the extended ideal `𝔪_R A`.

Proof: the special fibre `k ⊗[R] A` is smooth over the field `k`, hence reduced (Library theorem
`Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_of_domain`), and it is of
finite type. Suppose `a ∉ 𝔪_R A`. Mathlib's isomorphism
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor` identifies `A ⧸ 𝔪_R A` with `k ⊗[R] A`,
so `1 ⊗ a ≠ 0`. By `exists_algHom_ne_zero` there is a `k`-point `φ` with `φ (1 ⊗ a) ≠ 0`. The
composite `A → k ⊗[R] A → k` is an `R`-algebra map to the residue field. It lifts to an `R`-point
`σ : A →ₐ[R] R` by the Library's Henselian lifting theorem
`Langlands.CommutativeAlgebra.HenselianSections.exists_lift_of_smooth`. The residue of `σ a` is
`φ (1 ⊗ a) ≠ 0`, which contradicts `σ a ∈ 𝔪_R`.

`dvd_of_forall_dvd_pow`: assume in addition that `R` is a domain and `𝔪_R = (ϖ)` with `ϖ ≠ 0`.
If `ϖ ^ n` divides `σ g` for every `R`-point `σ`, then `algebraMap R A (ϖ ^ n)` divides `g`.

Proof: induction on `n`. In the successor step the key lemma gives `g = ϖ g'`. Cancelling `ϖ`
in the domain `R` shows that `ϖ ^ n` divides every `σ g'`, and the induction hypothesis
applies to `g'`.

## Discrete valuation rings

`dvd_of_forall_dvd`: let `R` also be a discrete valuation ring and `s ≠ 0`. If `s` divides
`σ g` for every `R`-point `σ` of `A`, then `algebraMap R A s` divides `g`.

Proof: write `s = u ϖ ^ n` with `u` a unit and `ϖ` a uniformiser
(`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`). Apply `dvd_of_forall_dvd_pow` to
`ϖ ^ n`, then absorb `u⁻¹` into the quotient.

## Provenance

These are standard facts: rational points of reduced finite-type algebras over an algebraically
closed field (Hilbert's Nullstellensatz), and Hensel lifting of points on smooth algebras. Their
use for detecting integrality on smooth models follows the argument of Kaletha–Prasad
Proposition A.7.1. The Lean proofs combine Mathlib with the two Library theorems named above.
