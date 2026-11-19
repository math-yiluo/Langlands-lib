# Commutative algebra for the local comparison on finite pieces

Lean module: `Langlands.Geometry.Analytic.FinitePieceLocalAlgebra`
(namespace `Langlands.Analytic.AffineAnalytification.FinitePieceLocalAlgebra`). Support module
for Task 7655. Pure commutative algebra, with Mathlib imports only.

## Content

* `bijective_localRingHom_of_ker_le_pow`: let `C` be Noetherian and let `χ : C → S` be a
  surjective ring map. Suppose `ker χ ⊆ (χ⁻¹ n)^k` for every maximal ideal `n` of `S` and every
  `k`. Then for every prime `𝔰` of `S` the local map `C_(χ⁻¹ 𝔰) → S_𝔰` is bijective.
* `isIntegral_quotient_pow`, `finite_quotient_pow`: suppose every element of an `R`-algebra `C`
  satisfies a monic polynomial over `R` modulo an ideal `I`. Then every `C/I^k` is integral over
  `R`. If moreover `C` is of finite type over `R`, then `C/I^k` is a finite `R`-module.
* `exists_monic_aeval_mem_of_ker_le`: let `χ : C →ₐ[R] S` with `S` module-finite over `R`. Then
  every element of `C` satisfies a monic polynomial over `R` modulo any ideal containing `ker χ`.
* `isUnit_of_lift_eq_one`, `lift_pow_comap_aux`: let `p := χ⁻¹ J` and `k ≠ 0`. The map
  `C/p^k → T/J` induced by `χ` is well defined, and an element of `C/p^k` mapping to `1` is a
  unit.

## Proofs

* Bijectivity. Surjectivity is direct from surjectivity of `χ`. For injectivity, let `c/s` map to
  `0`, so `χ(t c) = 0` for some `t ∉ χ⁻¹ 𝔰`. Choose a maximal `n ⊇ 𝔰` and put `p := χ⁻¹ n`. Then
  `t c ∈ ⋂_k p^k`. The Krull intersection theorem in the form
  `Ideal.mem_iInf_smul_pow_eq_bot_iff` gives `r ∈ p` with `r (t c) = t c`. Then `1 - r ∉ p`, so
  `1 - r ∉ χ⁻¹ 𝔰`, and `(1 - r) t` kills `c`.
* Integrality modulo `I^k`: if `f(x) ∈ I`, then `f^k(x) ∈ I^k`. Finiteness then follows from
  finite type plus integrality (`Algebra.IsIntegral.finite`).
* Units: if `x ↦ 1` in `T/J`, then `x - 1 ∈ p`, so `(x - 1)^k = 0` in `C/p^k`, and
  `x = (x - 1) + 1` is a unit.

## Provenance

Internal. Standard commutative algebra (Krull intersection theorem, integrality, nilpotent
perturbations of units), packaged for the proof of
`AffineAnalytificationFinitePieceLocalStatement` in `FinitePieceLocalProof`.
