# The final algebraic steps of Landherr's theorem

Module: `Langlands.Algebra.CentralSimple.LandherrFinish`.

Let `E/F` be separable quadratic with `CharZero F`, `r = skewRoot F E`, `d = skewSq F E`,
`B` a finite-dimensional central simple `E`-algebra and `τ : FirstKindInvolution F B` acting
on `E` by the conjugation (`hτ`).

- `exists_eq_mul_of_diag_unit`: if `Z ᵗτ(Z) = diag(y, 1)` in `M₂(B)` for a unit `y`, then
  `y = x τ(x)` for a unit `x` of `B`. `exists_normOne_isUnit_sub` (module
  `Langlands.Algebra.CentralSimple.LandherrNormOneUnit`) gives `μ ∈ E` of norm one with
  `μ - Z₁₁` invertible; `μ` is central in `B` and `μ τ(μ) = 1` by `hτ`, so
  `exists_eq_mul_of_diag` (module `Langlands.Algebra.CentralSimple.LandherrCancellation`)
  gives `a` with `y = a τ(a)`, and `a` is a unit because `a (τ(a) y⁻¹) = 1`.
- `matrix_algebraMap_skewRoot`: `ᵗτ(r · 1) = -(r · 1)` in `M₂(B)`.
- `mul_matrix_eq_of_norm`: if `ᵗτ(y') = y'` and `X, Y ∈ F[y']` satisfy `X² - d Y² = y'`, then
  `Z = X + r Y` satisfies `Z ᵗτ(Z) = y'`. Indeed `ᵗτ` fixes `X` and `Y`
  (`involution_fix_adjoin`), `r` is central with `ᵗτ(r) = -r` and `r² = d`, and `X`, `Y`
  commute, so `(X + rY)(X - rY) = X² - d Y²`.

## Provenance

In the proof of Lemma 1 of §5.5 in Kneser, *Lectures on Galois Cohomology of Classical
Groups* (1969), printed pp. 72–73 (PDF pp. 78–79), the symmetric element `y' = t y τ(t)` is
written as `x τ(x)` with `x` in the commutative algebra `E[y'] ≅ E ⊗_F F[y']` by solving a
norm equation there; `Z = X + r Y` is this `x`, with `r = √d`. The cancellation step
`exists_eq_mul_of_diag_unit` then descends from `M₂(B)` to `B`.
