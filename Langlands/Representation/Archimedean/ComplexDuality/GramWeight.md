# Nondegeneracy of the integration pairing on `U(n)`

Module: `Langlands.Representation.Archimedean.ComplexDuality.GramWeight`.

## Purpose and provenance

This is internal infrastructure for the proof of
`Langlands.Archimedean.ComplexStandardDualityStatement`, namely its nondegeneracy clause. Let
`χ, χ'` be families of characters of `ℂˣ` with `χᵢ(z) χ'ᵢ(z) = 1`, and suppose
`|χᵢ(z)|² = |z|²^(sᵢ)` for real numbers `sᵢ`. For every nonzero `U(n)`-finite function `h` in
the principal series `principalSeries ℂ n χ'`, the module constructs a `U(n)`-finite function `f`
in `principalSeries ℂ n χ` with `∫_{U(n)} f h ≠ 0`.

In the literature this is the nondegeneracy of the standard pairing between principal series
induced from inverse characters. Its usual proof restricts to `K`, using the isomorphism of the
`K`-finite principal series with `K`-finite functions on `K`. The Library has no such
restriction isomorphism, so this module builds the partner `f` explicitly. Its route uses
Gram determinants and is an auxiliary device of this formalization. The facts used (the
Iwasawa decomposition `GL_n(ℂ) = B·U(n)` and multiplicativity of determinants) are standard,
so the module cites no literature.

## Proof route

1. **Iwasawa decomposition.** The Library lemma
   `Langlands.LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_unitary` writes
   `g = b w` with `b` invertible upper triangular and `w` unitary. Splitting `b = diag(a) u` with
   `u` upper unipotent gives `g = diag(a) · u · k` with `k ∈ U(n)`. Consequently, a function of a
   principal series that vanishes on `U(n)` vanishes identically.
2. **Gram determinants.** For a matrix `y` and `0 ≤ m ≤ n`, let `Yₘ` consist of the rows
   `m, …, n-1` of `y` and put `Rₘ(y) = Re det(Yₘ Yₘᴴ)`, so `Rₙ = 1`. Right multiplication by a
   unitary matrix does not change `Yₘ Yₘᴴ`, and `Rₘ(1) = 1`. For `b` upper triangular, the rows
   `m, …` of `b y` are the lower-right block of `b` times `Yₘ`, so
   `Rₘ(b y) = ∏_{l ≥ m} |b_ll|² Rₘ(y)`. By the Iwasawa decomposition, `Rₘ` is a positive real
   number on `GL_n(ℂ)`. Since `det(Yₘ Yₘᴴ)` is a polynomial in the real and imaginary parts of
   the entries, `Rₘ` is smooth.
3. **The Gram weight.** `ψₛ(y) = ∏_{m < n} (Rₘ(y) / Rₘ₊₁(y))^(sₘ)` (real powers). It is smooth on
   `GL_n(ℂ)`, right `U(n)`-invariant, equal to `1` on `U(n)`, and satisfies
   `ψₛ(diag(a) u g) = ∏ₘ |aₘ|²^(sₘ) ψₛ(g)`.
4. **The partner.** `partner s h = ψₛ · conj h`. It is smooth. Since
   `|χₘ(aₘ)|² conj(χ'ₘ(aₘ)) = χₘ(aₘ) conj(χₘ(aₘ) χ'ₘ(aₘ)) = χₘ(aₘ)`, and the modulus factor of
   the principal-series character is a real power of a positive real number (hence fixed by
   conjugation), `partner s h` transforms by the character of `χ` whenever `h` transforms by the
   character of `χ'`. Right translation by `k ∈ U(n)` commutes with `partner s`, and `partner s`
   is additive and conjugate-linear. So it maps the span of the translates of `h` into the span
   of the images of a finite spanning set, and `partner s h` is `U(n)`-finite whenever `h` is.
5. **Nondegeneracy.** On `U(n)`, `partner s h · h = |h|²`. If `h ≠ 0`, then `h` is nonzero at
   some point of `U(n)` by step 1, so `∫_{U(n)} |h|² > 0` by continuity (`integral_unitaryHaar_pos`).
6. **Position characters.** For a list `ds` of complex character data, the Library's
   `ComplexCharacterData.character_eq` gives `|χ_d(z)| = |z|^(2 Re t)`. Hence the position
   characters `complexPositionCharacter ds` satisfy the hypothesis of step 4, with `sᵢ` twice the
   real part of the `i`-th exponent (and `0` past the end of the list).

## Declarations

All declarations are in the namespace `Langlands.Archimedean.ComplexDuality`. Here
`GL_n(ℂ) = Langlands.GeneralLinear n ℂ` and `U(n) = unitaryCompact ℂ n`.

- `exists_diagonalUnits_mul_upperUnipotent_mul_unitary g`: every `g ∈ GL_n(ℂ)` is
  `Iwasawa.diagonalUnits a * u * k` with `u ∈ upperUnipotent n ℂ` and `k ∈ U(n)`.
- `eq_zero_of_mem_principalSeries_of_eqOn`: a function in `principalSeries ℂ n χ` vanishing on
  `U(n)` is zero.
- `tailRows m y` (definition): the rows of `y` with index `≥ m`, as a matrix indexed by
  `{j : Fin n // m ≤ j}`.
- `tailGram m y` (definition): `det (tailRows m y * (tailRows m y)ᴴ)`.
- `tailRows_mul`, `tailGram_mul_unitary`, `tailGram_one`: `tailRows m (y * x) = tailRows m y * x`;
  `tailGram m` is invariant under right multiplication by unitary matrices; `tailGram m 1 = 1`.
- `tailRows_upper_mul`, `det_submatrix_tail`, `tailGram_upper_mul`: for upper triangular `b`,
  `tailRows m (b * y)` is the lower-right block of `b` times `tailRows m y`. That block has
  determinant `∏_{i ≥ m} b i i`, and `tailGram m (b * y) = ∏_{i ≥ m} |b i i|² · tailGram m y`.
- `val_diagonalUnits_mul`, `tailGram_borel_mul`: the same scaling for `b = diag(a) u`, with
  factor `∏_{i ≥ m} |a i|²`.
- `exists_tailGram_eq_pos`: on `GL_n(ℂ)`, `tailGram m` is a positive real number.
- `gramMinor m y` (definition): the real part of `tailGram m y`. `ofReal_gramMinor` and
  `gramMinor_pos` say it equals `tailGram m` on `GL_n(ℂ)` and is positive there;
  `gramMinor_borel_mul` is the Borel scaling.
- `prod_tail_succ`: splits `∏_{i ≥ m}` as the factor at `m` times `∏_{i ≥ m+1}`.
- `gramWeight s y` (definition): `∏_{m : Fin n} (gramMinor m y / gramMinor (m+1) y) ^ s m`.
- `gramWeight_mul_unitary`, `gramWeight_unitary`, `gramWeight_borel_mul`: right
  `U(n)`-invariance, value `1` on unitary matrices, and
  `gramWeight s (diag(a) u g) = ∏ₘ |aₘ|²^(sₘ) · gramWeight s g`.
- `contDiff_tailGram`, `contDiffAt_gramWeight`: `tailGram m` is smooth on all matrices and
  `gramWeight s` is smooth at every invertible matrix.
- `partner s h` (definition): `g ↦ gramWeight s g · conj (h g)`.
- `conj_cpow_ofReal`, `normSq_mul_star_principalSeriesCharacter`: conjugation fixes the modulus
  factors, and `∏ₘ |aₘ|²^(sₘ) · conj (principalSeriesCharacter ℂ n χ' a) =
  principalSeriesCharacter ℂ n χ a` when `χᵢ χ'ᵢ = 1` and `|χᵢ(z)|² = |z|²^(sᵢ)`.
- `partner_mem_principalSeries`: under these hypotheses `partner s` maps
  `principalSeries ℂ n χ'` into `principalSeries ℂ n χ`.
- `partner_rightTranslation`, `partner_zero`, `partner_add`, `partner_smul`, `partner_mem_span`:
  `partner s` commutes with right translation by `U(n)`, is additive and conjugate-linear, and
  maps spans into spans of images.
- `partner_mem_kFiniteVectors`: `partner s` preserves `U(n)`-finiteness under right translation.
- `exists_integral_mul_ne_zero`: for `χᵢ χ'ᵢ = 1` and `|χᵢ(z)|² = |z|²^(sᵢ)`, every nonzero
  `h` in `kFiniteFunctions (principalSeries ℂ n χ') (unitaryCompact ℂ n)` has some
  `f` in `kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)` with
  `∫ k, f k * h k ∂(unitaryHaar n) ≠ 0`.
- `exists_normSq_complexPositionCharacter ds`: there are real `sᵢ` with
  `|complexPositionCharacter ds i z|² = |z|²^(sᵢ)` for all `i` and `z`.
