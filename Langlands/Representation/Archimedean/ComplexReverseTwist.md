# The twist `g ↦ w₀ (gᵀ)⁻¹` of `GL_n(ℂ)` and the principal series

Lean module: `Langlands.Representation.Archimedean.ComplexReverseTwist`, namespace
`Langlands.Archimedean.ComplexReverseTwist`. Worker 5677 wrote it under Task 7064 as a helper for
`ComplexStrictReverseIntertwinerKernelStatement` (module `ComplexReverseIntertwinerStrict`).

Notation. `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `U(n)` is `unitaryCompact ℂ n` with the Haar
probability measure `ComplexDuality.unitaryHaar n`, `principalSeries ℂ n χ` is the smooth
principal series of the characters `χ_0, …, χ_{n-1}` of `ℂˣ` (functions with
`f(a u g) = principalSeriesCharacter ℂ n χ a · f(g)` for diagonal `a` and upper unipotent `u`),
and `kFiniteFunctions … (unitaryCompact ℂ n)` its `U(n)`-finite part.

## Definitions

- `w0Mat n`, `w0GL n`: the antidiagonal permutation matrix `w₀` (`w₀ i j = 1` iff `i = n-1-j`), as
  a matrix and as an element of `GL_n(ℂ)`.
- `transposeGL g = gᵀ` on `GL_n(ℂ)`.
- `conjAut g = (gᵀ)⁻¹`, a monoid homomorphism `GL_n(ℂ) → GL_n(ℂ)`; `conjK n` is its restriction
  `U(n) → U(n)`.
- `twist g = w₀ (gᵀ)⁻¹`.
- `twistLin n f = f ∘ twist`, a `ℂ`-linear map on functions `GL_n(ℂ) → ℂ`.

## Results

- Algebra of `w₀`: `w0Mat_mul_apply`, `mul_w0Mat_apply`, `w0Mat_mul_mul_w0Mat_apply`
  (`(w₀ M w₀)_{ij} = M_{n-1-i, n-1-j}`), `w0Mat_mul_self` (`w₀² = 1`), `w0Mat_transpose`,
  `star_w0Mat`, `w0GL_mul_self`, `w0GL_inv`, `w0GL_mem` (`w₀ ∈ U(n)`).
- Transposition: `transposeGL_mul` (`(gh)ᵀ = hᵀ gᵀ`), `transposeGL_transposeGL`, `transposeGL_inv`,
  `transposeGL_w0GL`, `continuous_transposeGL`, `transposeGL_mem` (`U(n)` is stable).
- `conjAut`: `conjAut_conjAut` (involution), `conjAut_transposeGL` (`conjAut gᵀ = g⁻¹`),
  `conjAut_w0GL`, `continuous_conjAut`, `conjAut_mem`.
- The twist: `twist_mul` (`twist(gh) = twist(g) conjAut(h)`), `twist_twist` (involution),
  `twist_one` (`twist 1 = w₀`), `twist_mul_transposeGL` (`twist(g hᵀ) = twist(g) h⁻¹`), `twist_mem`,
  `continuous_twist`.
- `map_conjK_unitaryHaar`: the Haar probability measure of `U(n)` is invariant under `conjK`
  (the image measure is again a Haar probability measure).
- `integral_twist`: `∫_{U(n)} F(twist κ) dκ = ∫_{U(n)} F(κ) dκ` for continuous `F`
  (invariance under `conjK`, then left invariance under `w₀`).
- `integral_mul_inv_eq_twist`: for continuous `a`, `b` and `g ∈ GL_n(ℂ)`,
  `∫ a(κ g⁻¹) b(κ) dκ = ∫ a(twist(κ gᵀ)) b(twist κ) dκ` (from `twist_mul_transposeGL` and
  `integral_twist`).
- `twistLin_apply`, `twistLin_twistLin`, `contMDiff_twistLin` (smoothness is preserved; the
  extension `y ↦ f(w₀ (y⁻¹)ᵀ)` to matrices is smooth on the invertible ones).
- `w0_conj_diagonal`: `w₀ ((a⁻¹)ᵀ) w₀ = diag(a_{n-1}⁻¹, …, a_0⁻¹)` for `a = diag(a_0, …, a_{n-1})`;
  `w0_conj_upperUnipotent`: `w₀ ((u⁻¹)ᵀ) w₀` is upper unipotent for upper unipotent `u`;
  `twist_diagonal_mul`: `twist(a u g) = diag(a_{n-1-i}⁻¹) · u' · twist(g)` with that `u'`.
- `norm_inv_cpow`, `principalSeriesCharacter_rev_inv`: if `χ'_j(z) = χ_{n-1-j}(z⁻¹)` for all `j`,
  then the principal series character of `χ` at `(a_{n-1-i}⁻¹)_i` equals that of `χ'` at `a`
  (after reindexing `i ↦ n-1-i`, the factor `(|a_i|²)^{(n-1)/2 - i}` of the character becomes
  `(|a_i⁻¹|²)^{-((n-1)/2 - i)}`, which is the same number).
- `twistLin_mem_principalSeries`: under the same hypothesis on `χ'`, `f ∘ twist` lies in the
  principal series of `χ'` when `f` lies in that of `χ`.
- `rightTranslation_twistLin`: `R(k)(f ∘ twist) = (R(conjAut k) f) ∘ twist`.
- `twistLin_mem_kFiniteFunctions`: the twist also preserves `U(n)`-finiteness (the `U(n)`-span of
  `f ∘ twist` lies in the image under `twistLin` of the `U(n)`-span of `f`, since `conjK` is
  surjective onto `U(n)`).

## Provenance

Derived (internal). Standard facts about the Chevalley-type involution `g ↦ w₀ (gᵀ)⁻¹` of
`GL_n` and the invariance of Haar measure, formalized for this project. No statement from the
literature is introduced; all results are proved here.
