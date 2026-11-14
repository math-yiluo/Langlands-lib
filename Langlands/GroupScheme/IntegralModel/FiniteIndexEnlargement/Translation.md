# Translations of coordinates by generic points

Worker 33, task `e1575004-9fac-4821-9bc9-ddcb15e7cbf3` (Task 6018). This is an internal helper
module for the proof of
`Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementStatement`. Its definitions are
auxiliary constructions for that proof. They are derived, not taken from a source.

## Integral criterion for `K ⊗[R] C`

Let `R` be a commutative ring with an algebra `K` over it, and `C` an `R`-algebra.

- `pointExt σ : K ⊗[R] C →ₐ[R] K` is the `K`-linear extension `c ⊗ x ↦ c · σ x` of an integral
  point `σ : C →ₐ[R] R`. It is Mathlib's `Algebra.TensorProduct.productMap` of the identity of
  `K` and `ofId ∘ σ`.
- `exists_smul_eq_tmul`: if `R` is a domain with fraction field `K`, every `t : K ⊗[R] C`
  satisfies `s • t = 1 ⊗ g` for some nonzero `s : R` and some `g : C`. The proof is induction on
  `t`: clear denominators for pure tensors and multiply the denominators for sums.
- `exists_pow_eq_mul`: in a discrete valuation ring, every nonzero `s` divides some power of a
  uniformiser `ϖ`.
- `exists_tmul_eq_of_forall` (integral criterion): let `R` be a Henselian discrete valuation ring
  with algebraically closed residue field and fraction field `K`, and let `C` be smooth over `R`.
  If `pointExt σ t ∈ R` for every integral point `σ`, then `t = 1 ⊗ c` for some `c : C`.
  Proof: write `s • t = 1 ⊗ g`. Then `s` divides `σ g` for every `σ`, so by
  `dvd_of_forall_dvd` (module `IntegralPoints`) `g = s c` in `C`. Hence `s • (1 ⊗ c) = s • t`,
  and multiplying by `s⁻¹ ∈ K` gives `1 ⊗ c = t`.

## Translations

Now let `A` be a commutative Hopf algebra over `R`, let `P` be a group, and let
`ev : P →* WithConv (A →ₐ[R] K)` be a monoid homomorphism into Mathlib's convolution monoid of
`K`-valued points. So `ev (x * y)` is the convolution product
`(ev x ⊗ ev y) ∘ Δ` (`ev_mul_ofConv`), and `ev 1` is `algebraMap ∘ counit` (`ev_one_apply`).

- `evalExt ev y : K ⊗[R] A →ₐ[R] K` is `c ⊗ a ↦ c · ev y a`.
- `leftTrans ev x : A →ₐ[R] K ⊗[R] A` is `(ev x ⊗ id) ∘ Δ`, the coordinate `y ↦ a (x * y)` with
  coefficients in `K`.
- `rightTrans ev x` is `(id ⊗ ev x) ∘ Δ` followed by the swap `A ⊗ K ≅ K ⊗ A`, the coordinate
  `y ↦ a (y * x)`.

`evalExt_leftTrans` and `evalExt_rightTrans` state `evalExt ev y (leftTrans ev x a) =
ev (x * y) a` and `evalExt ev y (rightTrans ev x a) = ev (y * x) a`. They follow from
`ev_mul_ofConv` by checking on pure tensors.

## Translation lemmas

Assume further that `R` is a Henselian discrete valuation ring with algebraically closed residue
field and fraction field `K`, and that `A` is smooth over `R`. Let `U ≤ P` be a subgroup with

- `hU`: `x ∈ U` iff `ev x a ∈ R` for every `a : A`, and
- `hsurj`: every integral point `σ : A →ₐ[R] R` has the form `ofId ∘ σ = ev u` for some `u`.

Then:

- `exists_tmul_eq_of_forall_mem`: if `t : K ⊗[R] A` has `evalExt ev u t ∈ R` for every `u ∈ U`,
  then `t = 1 ⊗ b` for some `b : A`. Proof: by `hsurj` and `hU`, each `pointExt σ` equals some
  `evalExt ev u` with `u ∈ U`; then apply the integral criterion.
- `exists_leftTrans_eq` and `exists_rightTrans_eq`: if `ev (x * u) a ∈ R` (resp.
  `ev (u * x) a ∈ R`) for every `u ∈ U`, then the left (resp. right) translate of `a` by `x`
  equals `1 ⊗ b` for some `b : A`.
- `exists_left_translate`: under the same hypothesis there is `b : A` with
  `ev y b = ev (x * y) a` for every `y : P`.
- `exists_pow_smul_mem`: for a uniformiser `ϖ`, any `x : P` and `a : A`, there is `N` with
  `ϖ ^ N • ev (x * u) a ∈ R` for all `u ∈ U`. Proof: write `s • leftTrans ev x a = 1 ⊗ g`. Then
  `s • ev (x * u) a = ev u g` is integral for `u ∈ U`, and `s` divides a power of `ϖ`.

Points do not separate elements of `K ⊗[R] A` in general. For this reason every identity above
is proved algebraically, never by comparing values.
