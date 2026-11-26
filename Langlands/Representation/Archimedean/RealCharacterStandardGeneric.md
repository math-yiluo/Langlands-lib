# Real character standard modules are generic

Module `Langlands.Representation.Archimedean.RealCharacterStandardGeneric`.

## Results

- `Langlands.Global.RankinSelbergGlobal.RealGodement.exists_canonicalJacquetMap_weylLong_ne_zero`:
  for every `r`, every `a : ℝˣ`, every parity vector `p : Fin (r + 1) → Fin 2` and every
  exponent vector `z : Fin (r + 1) → ℂ`, some vector `f` of the `O(r+1)`-finite standard module
  of `characterList p z` has `canonicalJacquetMap a p z f (weylLong (r + 1) ℝ) ≠ 0`.
- `Langlands.Archimedean.RealCharacterStandardGeneric.rightDerivative_one_of_whittaker`: let
  `W` be a smooth function on `GL_{r+1}(ℝ)` with `W(u g) = realWhittakerCharacter a u · W(g)` for
  every upper unipotent `u`. For a strictly upper triangular real matrix `X`, the right
  derivative of `W` along `X` at the identity is `2π i a (∑ᵢ X_{i,i+1}) · W(1)`.
- `Langlands.Archimedean.isRealGeneric_characterList`: for every `r`, `p` and `z`,
  `IsRealGenericGKModule (r + 1) (realStandardLie (r + 1) (characterList p z))`.

`characterList p z` is the Library's list of real character blocks with parities `p` and
exponents `z` (module `Langlands.Global.RankinSelberg.RealGodementCompactProfile`), so the last
theorem says that the `O(n)`-finite principal series of any real characters, `n ≥ 1`, carries a
nonzero Whittaker functional for a nondegenerate unitary character, in the algebraic sense of
`IsRealGenericGKModule`.

## Proofs

**Nonvanishing at the long Weyl element.** The proof is that of the Library theorem
`realGodementCanonicalNonzero` (module `RealGodementCanonicalNonzero`), which already evaluates
at the long Weyl element; the statement here records that value. In rank one
`weylLong 1 ℝ = 1`, `characterList p z` is a single character block, and on the strict spectral
chamber (all of `ℂ` in rank one) the canonical map is the rank-one Jacquet integral, which is the
evaluation of the section; the character vector of `RealRankOneStandardModule` takes the value
`1` at the identity. In rank `t + 2`, `realGodementCanonicalNonzero` for rank `t + 1` gives a
lower vector with nonzero canonical coefficient. `realGodementPolynomialTest` and
`realGodementFiniteCompactTest` produce a finite compact test frame, and the canonical column
formula `realGodementCanonicalColumn` identifies the value at `weylLong (t + 2) ℝ` of the
canonical coefficient of the lifted frame vector with the nonzero leading value of the test.

**Derivative at the identity.** By `rightDerivative_eq_fderiv_mul_left` the right derivative is
the derivative at `1` of the extension of `W` to all matrices, applied to `X`. Along the line
`t ↦ 1 + t X` (a curve of upper unipotent matrices, `unipotentLine`) the covariance gives
`W(1 + t X) = exp(2π i a t ∑ᵢ X_{i,i+1}) W(1)`, because the superdiagonal of `1 + t X` is `t`
times that of `X` and `realScaledCharacter a` is `x ↦ e^{2π i a x}` (`Real.fourierChar`).
Uniqueness of derivatives along this line gives the formula.

**Genericity.** Take `a = 1` and `B = canonicalJacquetMap 1 p z`. By `realGodementCanonicalModel`,
`B` is a uniform Whittaker intertwiner for the character `realWhittakerCharacter (-1)`: each
`B f` is smooth and left covariant, `B` commutes with right translation by `O(r+1)`, and
`B (π(1 ⊗ X) f)` is the right derivative of `B f` along `X`. The functional is
`ℓ(f) = (B f)(1)`.

- `ℓ ≠ 0`: for `f` with `(B f)(w₀) ≠ 0`, `w₀ = weylLong (r + 1) ℝ ∈ O(r+1)`
  (`RealEqualDualConvergence.weylLong_mem_unitary`), the right translate `f'` of `f` by `w₀` has
  `ℓ(f') = (B f)(w₀) ≠ 0` by compact equivariance.
- Whittaker identity: for strictly upper triangular `X`,
  `ℓ(π(1 ⊗ X) f) = (R(X) B f)(1) = 2π i (-1) (∑ᵢ X_{i,i+1}) ℓ(f)` by the derivative lemma. This
  is the identity of `IsRealGenericGKModule` with all coefficients `aᵢ = -2π`, which are nonzero.
  The private lemma `sum_superdiag_eq` rewrites `∑ᵢ X_{i,i+1}` as the double sum of the
  definition.

## Provenance

The canonical map `canonicalJacquetMap` is the Library's continued Jacquet integral, following
Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §7.2, p. 47 of the author-posted version
(`jacquet-2009-archimedean-rankin-selberg`): for `ℜu₁ < ⋯ < ℜuₙ` (his (7.3)) the Whittaker
functional `λ_u(f) = ∫_{Nₙ} f(v) \overline{θ_{ψ,n}(v)} dv`, with the complex conjugate of the
character `θ_{ψ,n}` of §2, equation (2.2), p. 3, converges, and it extends by analytic
continuation to all `u` and is never `0`. The Library's `additiveJacquetIntegral` uses the
positive phase `realScaledCharacter a` in its integrand instead of the conjugate, so its
continued map `canonicalJacquetMap a p z` transforms on the left by
`realWhittakerCharacter (-a)` (`realGodementCanonicalModel`); with `a = 1` this is the
character `-1` used above, and it gives the coefficients `aᵢ = -2π`. The nonvanishing used here
is the Library's own proof of the last assertion, read at the long Weyl element; its passage to
an algebraic Whittaker functional on the `O(n)`-finite vectors (evaluation at `1` and
differentiation of the covariance) is derived in this module.
