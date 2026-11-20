# Twisting complex principal series by a character of the determinant

Module `Langlands.Representation.Archimedean.ComplexStandardDeterminantTwist`, namespace
`Langlands.Archimedean.ComplexDeterminantTwist`. Author: Worker 5086 (Task 7783).

Local helper lemmas on `GL_n(ℂ)` for the twist rule of complex-place parameters
(`Langlands.Automorphic.ComplexPlaceParameterHeckeTwist`). Everything here is elementary and
internal; no source is cited. Nothing is assumed: every statement is proved.

## Definitions

- `detCharacter η g = η(det g)` for a continuous character `η : ℂˣ →ₜ* ℂˣ`, as a complex
  function on `GL_n(ℂ)`. The inverse character `η⁻¹` is the group inverse of continuous
  homomorphisms; `detCharacter_inv` says it gives the pointwise inverse.
- `detMul η` is the complex-linear map `f ↦ (g ↦ η(det g) · f g)` on all functions on
  `GL_n(ℂ)`.
- `kFiniteDetMul η h` is `detMul η` restricted to the `U(n)`-finite functions of the smooth
  principal series `principalSeries ℂ n χ`, with values in those of `principalSeries ℂ n χ'`.
  The hypothesis `h : ∀ (i : Fin n) z, χ' i z = χ i z * η z` says that the characters `χ'` are
  those of `χ` times `η` at every position `i < n`.

## Results

- Group-theoretic facts: `detCharacter_mul`, `detCharacter_one`, `detCharacter_ne_zero`,
  `detCharacter_inv`, `detCharacter_inv_mul`; `determinant_upperUnipotent` (unipotent
  determinant `1`) and `determinant_diagonalUnits` (determinant of `diag(a)` is `∏ aᵢ`), hence
  `detCharacter_borel`: `η(det(diag(a) u g)) = (∏ᵢ η(aᵢ)) · η(det g)`.
- `contMDiff_detCharacter`: `η ∘ det` is smooth in the matrix model. The proof composes the
  published smoothness of continuous characters of the units of a commutative real Banach
  algebra (`Langlands.Global.contDiffAt_unitsCharacterExtension`, applied to `A = ℂ`) with the
  smooth determinant.
- `principalSeriesCharacter_twist` and `detCharacter_mul_mem_principalSeries`: multiplication
  by `η ∘ det` maps `principalSeries ℂ n χ` into `principalSeries ℂ n χ'`. The modulus
  factor is unchanged, so the principal-series character gains the factor `∏ᵢ η(aᵢ)`, which
  is exactly `η(det(diag(a) u))`.
- `rightTranslation_detMul` and `detMul_mem_kFiniteVectors`: right translation by `k` of
  `η(det)·f` is `η(det k)` times `η(det)·(R_k f)`, so the span of the `K`-orbit of `η(det)·f`
  lies in the image of the span of the orbit of `f`; finite-dimensionality is preserved, for
  any subgroup `K`.
- `detMul_mem_kFiniteFunctions`, `coe_kFiniteDetMul`, `kFiniteDetMul_injective` (since
  `η(det g) ≠ 0`).
- `rightDerivative_detMul`: for smooth `f`,
  `R_X(η(det)·f)(g) = η(det g) · (R_X(η ∘ det)(1) · f(g) + R_X f(g))`, by the published product
  rule `ComplexTemperedComplement.rightDerivative_mul_fun` and left equivariance of the right
  derivative (`rightDerivative_mul_left_of_eq`).
- `rightDerivative_detCharacter_inv`: `R_X(η⁻¹ ∘ det)(1) = -R_X(η ∘ det)(1)`, by the product
  rule applied to the constant function `η⁻¹(det) · η(det) = 1`.
- `kFiniteDetMul_rightTranslation`: on `U(n)`-finite functions,
  `η(det)·(R_k f) = η(det k)⁻¹ · R_k(η(det)·f)` for `k ∈ U(n)`.
- `kFiniteDetMul_rightDerivative`: `η(det)·(R_X f) = R_X(η(det)·f) + (-R_X(η ∘ det)(1)) ·
  η(det)·f`. The membership proofs of the translated and differentiated functions are the
  published stability lemmas `rightTranslation_mem_kFiniteFunctions_principalSeries` and
  `rightDerivative_mem_kFiniteFunctions_principalSeries`.
- `complexPositionCharacter_map_mul`: for a list `ds` of complex character blocks and a block
  `d`, the position characters of `ds.map (·.mul d)` (each block multiplied by `d`, with the
  published `ComplexCharacterData.mul`) are those of `ds` times the character of `d`, at every
  position inside the list. `complexPositionCharacter_map_mul_inv` rewrites this for
  `ds.length = n` in the form `χ_ds = χ_{ds.map (·.mul d)} · d⁻¹` used with `η = d⁻¹`.

Positions past the end of the list carry the trivial character in
`complexPositionCharacter`, so the list statements require the position to lie inside the
list (or `ds.length = n`).
