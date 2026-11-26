# Real square matrix functional equation for determinant-twisted coefficients

**Provenance.** This is the form of the matrix zeta equation of Hervé Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §4.7, Proposition 4.4 (pp. 30–31), as it is used in §8.2 (pp. 54–58). There one needs `Z(s, Φ₀, f'ᵢ ⊗ μ_n)`, the matrix integral of a principal-series coefficient multiplied by a character of the determinant. It is internal to this formalization and uses the positive Fourier phase with parameter `b`. Jacquet's character `ψ_a` corresponds to `b = -a`.

Let `n = r + 1`. Take a Haar measure on `GL_n(ℝ)`, a sigma-finite Haar measure on `O(n)`, a smooth section `f` of the principal series of the position characters of `ds`, a linear form `ℓ` with `HasCompactDerivativeBound`, a real character datum `c`, a square matrix Schwartz test `Φ` and `b ∈ ℝˣ`. Put `F(g) = c(det g) ℓ(translate g f)`. `RealMatrixTwistedFunctionalEquationStatement` concerns the normalized integrals of `(F, Φ)` and of `(F ∘ inverse transpose, matrixTransform b Φ)`. They converge absolutely and are holomorphic on a common right half-plane, extend meromorphically to `ℂ`, and satisfy off a discrete set

`L(s) Md(1-s) = E(s) Ld(1-s) M(s)`.

Here `L = torusL e u` and `Ld = torusL e (-u)` with `eᵢ` the position sign plus the parity of `c` and `uᵢ` the position exponent plus the exponent of `c`. Also `E(s) = torusEpsilon e · ∏ᵢ χᵢ(b) c(b) · |b|^(n(s-1/2))`. The factors are those of the twisted position characters. The theorem does not compare them with Langlands-quotient factors, and it is not a Whittaker-model or Rankin–Selberg equation.

**Lean proof.** Split `c(det g) = sgn(det g)^p · |det g|^t` with `p, t` the parity and exponent of `c`. For the sign part, the determinant of `exp(tX)` is a square of a determinant and hence positive, so the sign is constant along every right exponential curve. Its right derivative vanishes and all right derivative words commute with multiplication by it. Multiplication by the sign maps the principal series of `ds` to that of the sign-twisted list and back, because the square of a sign character is one. Composing `ℓ` with the backward map therefore keeps the same compact derivative words and bound, since the sign has norm one. The coefficient of the forward image is `sgn(det g)^p ℓ(translate g f)`, so `RealMatrixCompactFunctionalEquationStatement` applies to the sign-twisted data. For the absolute part, the primal coefficient is multiplied by `|det g|^t` and the dual coefficient by `|det g|^(-t)`; inverse transpose inverts the determinant, which gives the dual factor `|det g|^(-t)`. By `realMatrixZeta_shift`, the twisted primal zeta integral at `z` is the original primal integral at `z + t`, and the twisted dual zeta integral at `z` is the original dual integral at `z - t`. `realMatrixEquation_shift` therefore takes the continuations `M(z + t)` and `Md(z - t)` and the factors `L(z + t)`, `Ld(z - t)` and `E(z + t)`. In the reflected equation the dual argument `(1 - s) - t` is `1 - (s + t)`, so the original codiscrete equation at `s + t` gives the new one at `s`. The common right half-plane `Re s > σ + |Re t|` is the intersection of `Re(s + t) > σ` and `Re(s − t) > σ`. Under the shift the gamma products and root-number factor become those of the exponents shifted by `t`.

**Public helper results.** The two halves of the proof are stated separately so that
`RealMatrixNormalizedGrowth` can reuse them.

- `exists_signTwist_coefficient`: for `ds`, `f`, `ℓ` with `HasCompactDerivativeBound` and a
  character datum `c`, there are a section `f'` and a linear form `ℓ'` with
  `HasCompactDerivativeBound` on the principal series of the sign-twisted list
  `twistedPositionList n ds (charData c.parity 0)`. They satisfy
  `c(det g) ℓ(translate g f) = |det g|^t ℓ'(translate g f')` for every `g`, with `t` the
  exponent of `c`. Here `f'` is the image of `f` under multiplication by the sign character, and
  `ℓ'` is `ℓ` composed with the backward multiplication.
- `torusL_signTwist_shift` and `torusL_neg_signTwist_shift`: the torus `L`-products of the
  sign-twisted list, evaluated at `s + t` and at `s − t` respectively, are the torus products
  `torusL e u s` and `torusL e (−u) s` of the twisted parameters `eᵢ`, `uᵢ` above.
- `realMatrixZetaKernel_shift` and `realMatrixZeta_shift`: if `F'(g) = |det g|^w F(g)` for all
  `g`, then `realMatrixZeta μ F' Φ s = realMatrixZeta μ F Φ (s + w)` at every `s`.
- `detPower_inverseTranspose`, `signCharacter_sq`, `signTwist_back`: the determinant-power and
  sign-character identities used above. `|det(ιg g)|^w = |det g|^(−w)`, the square of a sign
  character is one, and twisting the sign-twisted list back by the same sign gives the original
  position characters.

`realMatrixTwistedFunctionalEquation` combines `exists_signTwist_coefficient`,
`realMatrixCompactFunctionalEquation`, `realMatrixEquation_shift` and the two torus shift
identities.
