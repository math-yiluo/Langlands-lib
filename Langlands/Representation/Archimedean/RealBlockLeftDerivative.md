# Left derivatives and the block Fourier coefficients

Module: `Langlands.Representation.Archimedean.RealBlockLeftDerivative`, namespace
`Langlands.Archimedean.RealBlockDerivative`.

## Purpose and provenance

The block Fourier coefficients
`Φ_j(f)(g) = blockFourierCoefficient N p j f g = ∫₀^{2π} f(r_p(θ) g) e^{-ijθ} dθ`
(module `Langlands.Representation.Archimedean.StandardModule`) are integrals over the rotations
`r_p(θ) = blockRotation N p θ` in the coordinates `p, q = p + 1`. This module computes how
they behave under derivatives in upper triangular directions. For a function `φ` that is
equivariant on the left under the Borel subgroup, the derivative of `Φ_j(φ)` is a combination
of `Φ_{j-2}(φ)`, `Φ_j(φ)` and `Φ_{j+2}(φ)` (a "tridiagonal formula").

This module is internal infrastructure for the proof of
`Langlands.Archimedean.RealCharacterPairFiltrationStatement`. There the formula
gives the conditions under which a functional built from block Fourier coefficients is a
Jacquet functional, and the propagation of vanishing Fourier coefficients along paths in the
Borel subgroup. The formula is an elementary computation (the Lie algebra action on `K`-types
of a principal series of `GL_2(ℝ)`, written in rotation coordinates). It is derived and proved
here, and the module makes no literature assertion, so it has no literature sources. The
definitions `conj`, `kappa`, `upperPart`, `IsExpEquivariant` and `rotDeriv` are internal
notation for the proofs.

## Notation

Throughout, `h : p + 1 < N`, and `ia h`, `ib h : Fin N` are the indices `p` and `q = p + 1`
(module `RealBlockRotation`). `W = rotationGenerator N p = E_{q,p} - E_{p,q}`, `r = r_p(θ)`,
and `c = cos θ`, `s = sin θ`. For a matrix `A`, `u = A_pp - A_qq` and `v = A_pq`. For exponents
`α : Fin N → ℂ`, `S = ∑ᵢ αᵢ Aᵢᵢ` and `δ = α_p - α_q`. `φ̃ = unitsExtension φ` is the extension
of a function on `GL_N(ℝ)` to all matrices by zero (module `PrincipalSeriesStability`), whose
Fréchet derivative expresses derivatives of `φ`.

## Declarations

### Products with block rotations

- `blockRotation_mul_apply h θ M i k`: the entry `(i, k)` of `r M` is
  `c M_{p,k} - s M_{q,k}` for `i = p`, `s M_{p,k} + c M_{q,k}` for `i = q`, and `M_{i,k}`
  otherwise.
- `mul_blockRotation_apply h θ M i k`: the entry `(i, k)` of `M r` is
  `c M_{i,p} + s M_{i,q}` for `k = p`, `-s M_{i,p} + c M_{i,q}` for `k = q`, and `M_{i,k}`
  otherwise.

Both follow from the entries of `r` (`blockRotation_apply`) by evaluating the matrix product.

### Conjugating an upper triangular matrix by a block rotation

- `conj N p θ A` is the matrix `r_p(θ) A r_p(-θ)`, that is `r A r⁻¹`.
- `kappa h θ A` is the real number `κ(θ) = c s (A_pp - A_qq) - s² A_pq = c s u - s² v`.
- `conj_apply h θ A i k`: the entries of `conj` in terms of `r A`, from
  `mul_blockRotation_apply` with `cos(-θ) = c`, `sin(-θ) = -s`.
- `conj_lower h θ hA hik`: if `A` is upper triangular and `k < i`, the entry `(i, k)` of
  `r A r⁻¹` is `κ(θ)` when `(i, k) = (q, p)`, and `0` otherwise.
- `conj_diag h θ hA i`: if `A` is upper triangular, the diagonal entries of `r A r⁻¹` are
  `c² A_pp - c s A_pq + s² A_qq` at `p`, `s² A_pp + c s A_pq + c² A_qq` at `q`, and `A_ii`
  otherwise.

The proofs of `conj_lower` and `conj_diag` expand the entries with the two product formulas,
use `A_{i',k'} = 0` for `k' < i'` and finish with `ring`.

### The decomposition `r A r⁻¹ = U + κ W`

- `upperPart h θ A` is the matrix `U = r A r⁻¹ - κ(θ) W`.
- `upperPart_isUpperTriangular h θ hA`: `U` is upper triangular when `A` is. Below the
  diagonal, `W` has the single nonzero entry `W_{q,p} = 1`, which cancels the entry `κ` of
  `r A r⁻¹` (`conj_lower`).
- `upperPart_diag h θ A i`: `U` and `r A r⁻¹` have the same diagonal entries, since `W` has
  zero diagonal.
- `blockRotation_mul_mul h θ A g`: `r A g = (U + κ W)(r g)` as matrices, since
  `r A g = (r A r⁻¹)(r g)`.
- `sum_upperPart_diag h θ hA α`:
  `∑ᵢ αᵢ Uᵢᵢ = S - δ (s² u + c s v)`. The proof inserts the diagonal entries from
  `conj_diag` and uses `s² + c² = 1`.

### Functions with an exponential left equivariance

- `IsExpEquivariant α φ` is the predicate
  `φ(exp(diag x) u g) = exp(∑ᵢ αᵢ xᵢ) φ(g)` for all real vectors `x`, upper unipotent `u`
  and `g` (with `exp(diag x) = matrixExpUnit N (Matrix.diagonal x)`).
- `isExpEquivariant_of_mem_principalSeries hχ hf`: if the characters satisfy
  `χᵢ(eˣ) = exp(τᵢ x)`, every `f` in `principalSeries ℝ N χ` satisfies `IsExpEquivariant`
  with the `ρ`-shifted exponents `αᵢ = τᵢ + (N - 1)/2 - i`. This holds because
  `principalSeriesCharacter` multiplies the `χᵢ` by the modulus factors `|aᵢ|^{(N-1)/2 - i}`.
- `fderiv_upperTriangular_of_isExpEquivariant hφ hα k hU`: for `φ` smooth with
  `IsExpEquivariant α φ` and `U` upper triangular,
  `dφ̃_k(U k) = (∑ᵢ αᵢ Uᵢᵢ) φ(k)`. Proof: write `U = Δ + N'` with `Δ` diagonal and `N'`
  strictly upper triangular. Along the curve `Γ(t) = exp(tΔ)(1 + tN') k`, with `Γ(0) = k` and
  `Γ'(0) = U k`, the function `φ` equals `exp(t ∑ αᵢ Uᵢᵢ) φ(k)`, because
  `1 + tN' = unipotentLine N' t` is upper unipotent. Compare the two derivatives at `t = 0`.

### Differentiating along the rotations

- `rotDeriv N p φ g θ` is the number `dφ̃_{r g}(W r g)`.
- `hasDerivAt_blockRotation_mul h hφ g θ`: `θ ↦ φ(r_p(θ) g)` has derivative
  `rotDeriv N p φ g θ` at `θ`. This uses the closed form `rotMatrix` and its derivative
  `W · rotMatrix` (module `RealBlockRotation`).
- `continuous_rotDeriv hφ g`: `rotDeriv N p φ g` is continuous in `θ`, since `φ̃` is `C^∞` on
  the open set of invertible matrices.
- `fderiv_blockRotation_mul_mul h hφ hα hA g θ`: the pointwise decomposition, for `A` upper
  triangular:
  `dφ̃_{r g}(r A g) = (S - δ (s² u + c s v)) φ(r g) + κ(θ) dφ̃_{r g}(W r g)`.
  It combines `blockRotation_mul_mul`, linearity of the derivative,
  `fderiv_upperTriangular_of_isExpEquivariant` for `U`, and `sum_upperPart_diag`.
- `kappa_fourier_identity θ j S δ x y v`: an identity of functions of `θ`. Write
  `e_k(θ) = e^{-ikθ}`, `u = x - y`, `κ = c s u - s² v`, and
  `κ' = (c² - s²) u - 2 s c v`, the derivative of `κ`. Then
  `(S - δ(s² u + c s v)) e_j - (κ' e_j + κ e_j · (-ij))` equals
  `(S - δu/2 - i v j/2) e_j + ((u + iv)/4)(δ + j - 2) e_{j-2} + ((u - iv)/4)(δ - j - 2) e_{j+2}`.
  The proof writes `e_{j∓2} = e_j (c² - s² ± 2 i c s)` and finishes with `linear_combination`
  using `i² = -1` and `s² + c² = 1`.

### The tridiagonal formula

- `integral_fderiv_blockRotation_mul_mul h hφ hα hA g j`: for `φ` smooth with
  `IsExpEquivariant α φ`, `A` upper triangular, `g ∈ GL_N(ℝ)` and `j ∈ ℤ`,

  `∫₀^{2π} dφ̃_{r g}(r A g) e^{-ijθ} dθ =
    (S - δ u/2 - i v j/2) Φ_j(φ)(g) + ((u + iv)/4)(δ + j - 2) Φ_{j-2}(φ)(g)
      + ((u - iv)/4)(δ - j - 2) Φ_{j+2}(φ)(g)`.

  Proof: insert the pointwise decomposition. For the term `κ(θ) e^{-ijθ} rotDeriv`, integrate by
  parts (`intervalIntegral.integral_mul_deriv_eq_deriv_mul`). Here `rotDeriv` is the
  derivative of `θ ↦ φ(r_p(θ) g)`, and the boundary terms vanish because `κ(0) = κ(2π) = 0`.
  The resulting integrand equals the right side's integrand by `kappa_fourier_identity`, and
  the integral splits into the three Fourier coefficients. All integrands are continuous.
- `blockFourierCoefficient_rightDerivative h hφ hα hA g hX j`: if `g X = A g` with `A` upper
  triangular, then `Φ_j(R_X φ)(g)` equals the same right side, where
  `R_X φ = rightDerivative (matrixModel ℝ N) X φ`. Indeed
  `R_X φ(r g) = dφ̃_{r g}(r g X)` (`rightDerivative_eq_fderiv`) and `r g X = r A g`. For
  `g = 1` the condition is `X = A`.
- `hasDerivAt_blockFourierCoefficient_comp h hφ hα hγ hA hγ' j`: let `γ` be a path in
  `GL_N(ℝ)` whose matrix is `C¹` in `s`, with derivative `A γ(s₀)` at `s₀` for an upper
  triangular `A`. Then `s ↦ Φ_j(φ)(γ s)` has at `s₀` the derivative given by the same right
  side at `g = γ s₀`. Proof: the integrand
  `(s, θ) ↦ φ̃(rotMatrix θ · γ s) e^{-ijθ}` is `C¹` on `ℝ × ℝ`, so the Library's
  `hasDerivAt_intervalIntegral_of_contDiff` (module `RealStandardModuleFourier`)
  differentiates under the integral. The `s`-derivative of the integrand at `s₀` is
  `dφ̃_{r γ(s₀)}(r A γ(s₀)) e^{-ijθ}`, and `integral_fderiv_blockRotation_mul_mul` evaluates
  its integral.
