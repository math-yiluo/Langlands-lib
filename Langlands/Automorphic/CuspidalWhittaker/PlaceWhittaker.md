# Whittaker functionals on place-stable subspaces of cuspidal realizations

Module `Langlands.Automorphic.CuspidalWhittaker.PlaceWhittaker`. Worker 174 wrote it for
Task 5996 (`e3f48d66-76bc-4321-a8ea-e25681c89d3f`, published under Task 5720). It proves the
Library statement `Langlands.Automorphic.CuspidalArchimedeanWhittakerFunctionalStatement`
(module `Langlands.Automorphic.CuspidalArchimedeanPlaceComponent`) as
`Langlands.Automorphic.cuspidalArchimedeanWhittakerFunctional`.

The statement: let `F` be a number field with compact adele quotient, `r : ℕ`, and `S` a
cuspidal operator realization of `GL_{r+1}`. At a real place `v`, every subspace `W ≠ ⊥` of `S`
stable under the compact action of `O(r+1)` and the Lie action of `𝔤𝔩_{r+1}(ℝ)` at `v`
satisfies `PlaceComponent.IsRealGeneric`. That is, there are coefficients `aᵢ ∈ ℝ`, nonzero for
`i + 1 < r + 1`, and a linear form `ℓ` on `S`, nonzero at a vector of `W`, with
`ℓ (π_v(1 ⊗ X) x) = i (∑ᵢ aᵢ X_{i,i+1}) ℓ x` for every strictly upper triangular real `X` and
every `x ∈ W`. At a complex place the same holds with `U(r+1)`, complex `aᵢ` and
`i · Re(∑ᵢ aᵢ X_{i,i+1})` (`IsComplexGeneric`).

The proof uses the helper modules `MixedTraceFormula`, `CurveDerivative` and
`ArchimedeanFunctional` of the same directory. All declarations below are in the namespace
`Langlands.Automorphic.CuspidalWhittaker`, except the final theorem.

## Proof outline

1. Take `x₀ ∈ W` nonzero. Its realized form `W_{x₀}` has a nonzero iterated Whittaker
   coefficient at some `g₀` (Library `exists_descend_ne_zero`).
2. Write the `v`-component of `g₀` as `b k`, with `b` upper triangular and `k` orthogonal
   (real place) or unitary (complex place). Put `h = g₀ · k⁻¹` and `x₁ = R_v(k) x₀ ∈ W`.
   Then `ℓ_h(x₁) = W_{x₀}(g₀) ≠ 0`, where `ℓ_h : x ↦ W_x(h)`.
3. The `v`-component of `h` is `B = b`. For a matrix unit `X = E_{pq}` with `p < q` at `v`,
   the Lie derivative formula of `ArchimedeanFunctional` gives
   `ℓ_h(X · x) = 2π i · Tr(∑ᵢ (B X B⁻¹)_{i,i+1}) · ℓ_h(x)`.
4. Because `B` and `B⁻¹` are upper triangular, the superdiagonal sum of `B E_{pq} B⁻¹` is
   `δ_{q,p+1} B_{pp} (B⁻¹)_{p+1,p+1}`.
5. Summing over matrix units gives the Whittaker identity. The coefficients are
   `aₚ = 2π B_{pp} (B⁻¹)_{p+1,p+1}` at a real place and `4π B_{pp} (B⁻¹)_{p+1,p+1}` at a
   complex place. They are nonzero since `B_{pp} (B⁻¹)_{pp} = 1`.

## Matrix units (section `MatrixUnits`, over a commutative ring)

- `mul_single_mul_apply`: `(B E_{pq}(c) B')_{ij} = B_{ip} c B'_{qj}`, where
  `E_{pq}(c) = Matrix.single p q c`.
- `conj_single_apply_eq_zero`: if `B`, `B'` are upper triangular and `p < q`, then
  `(B E_{pq}(c) B')_{ij} = 0` for `j ≤ i`. A nonzero term needs `i ≤ p < q ≤ j`.
- `conj_single_superdiag_eq_zero` and `sum_superdiag_conj_single`: under the same hypotheses
  on `Fin (r+1)`, `∑_{i<r} (B E_{pq}(c) B')_{i,i+1} = B_{pp} c B'_{qq}` if `q = p + 1`, and `0`
  otherwise. The `i`-th term vanishes unless `i ≤ p` and `q ≤ i + 1`, which forces `i = p` and
  `q = p + 1`.
- `diag_mul_diag_eq_one`: if `B`, `B'` are upper triangular with `B B' = 1`, then
  `B_{pp} B'_{pp} = 1`. Only the term `k = p` of `(B B')_{pp}` survives.
- `isUpperTriangular_of_mul_eq_one`: a right inverse of an upper triangular matrix is upper
  triangular. It is the inverse (`Matrix.inv_eq_right_inv`), and Mathlib's
  `blockTriangular_inv_of_blockTriangular` applies.
- `sum_sum_superdiag_single`: `∑ᵢ ∑ⱼ [j = i + 1] aᵢ E_{pq}(c)_{ij} = [q = p + 1] aₚ c`.

## From matrix units to Whittaker functionals (section `Abstract`)

`isRealWhittakerFunctional_of_single`: let `π` be a Lie action of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` on `V`. If
`ℓ (π(1 ⊗ E_{pq}(c)) x) = i · [q = p + 1] aₚ c · ℓ x` for all `p < q`, `c` and `x ∈ W`, then
`PlaceComponent.IsRealWhittakerFunctional π W a ℓ`.

- A strictly upper triangular `X` is `∑_{p,q} E_{pq}(X_{pq})` (`Matrix.matrix_eq_sum_single`).
- Both sides are additive in `X`, through `1 ⊗ (·)`, `π`, the evaluation at `x` and `ℓ`.
- Terms with `q ≤ p` vanish on both sides, since then `X_{pq} = 0` and `q ≠ p + 1`.
- The remaining terms are the hypothesis, and the sum is `sum_sum_superdiag_single`.

`isComplexWhittakerFunctional_of_single` is the same with complex `c`, `aₚ` and real parts
(`Complex.re_sum`).

## Place coordinates (section `Coordinates`)

- `placeMatrix φ h`, for a ring map `φ` from the mixed space (the Library's `realCoord v` or
  `complexCoord v`), is the image under `φ` of the archimedean component of `h` in mixed
  coordinates. This is a definition for this proof (internal provenance).
  `placeMatrix_mul_inv` states that its value and the value of its inverse multiply to `1`.
- `mapMatrix_conjDirection`: `φ` applied to `conjDirection h Y = A M A⁻¹` is
  `placeMatrix φ h · φ(M) · (placeMatrix φ h)⁻¹`, since `φ.mapMatrix` is multiplicative.
- Six lemmas compute `φ(M)` for `M` the matrix of the Library's place Lie inclusions
  `realPlaceLieInclusion v X` and `complexPlaceLieInclusion v X`: the coordinate at `v` is
  `X`, and the coordinates at every other place are `0`. They come from the Library's
  `realProjection_realInclusion` and its three analogues. `archimedeanMatrix_ext` says that
  archimedean matrices are determined by their coordinates at all places.
- `conjDirection_realPlace_apply`: the entries of `conjDirection h (realPlaceLieInclusion v X)`
  are `(Pi.single v (B X B⁻¹)_{ij}, 0)`, with `B = placeMatrix (realCoord v) h`.
  `conjDirection_complexPlace_apply` is the complex analogue, `(0, Pi.single v (B X B⁻¹)_{ij})`.
- `realLieAlgebraToMatrix_realPlace_mul_self` and `realLieAlgebraToMatrix_complexPlace_mul_self`:
  if `X * X = 0` then the archimedean matrix of the included direction squares to zero
  (checked at every place).
- `realWhittakerCoeff h v p = 2π B_{pp} (B⁻¹)_{p+1,p+1}` and
  `complexWhittakerCoeff h v p = 4π B_{pp} (B⁻¹)_{p+1,p+1}` for `p + 1 < r + 1`, and `1` for
  the last index. These are definitions for this proof (internal provenance).
- `mixedTrace_conjDirection_realPlace`: the mixed trace of the superdiagonal of the conjugated
  direction is `∑ᵢ (B X B⁻¹)_{i,i+1}` (linearity and `mixedTrace_single_real`).
  `mixedTrace_conjDirection_complexPlace` gives `2 Re ∑ᵢ (B X B⁻¹)_{i,i+1}`
  (`mixedTrace_single_complex`).
- `two_pi_mul_realSuperdiag` and `two_pi_mul_complexSuperdiag` identify
  `2π · [q = p + 1] B_{pp} c (B⁻¹)_{qq}` with `[q = p + 1] aₚ c`. In the complex case they
  identify `2π · 2 Re(…)` with `Re([q = p + 1] aₚ c)`.

## The realization (section `Realization`)

- `realizationFunctional_realPlaceLieAction_single`: if `B = placeMatrix (realCoord v) h` is
  upper triangular and `p < q`, then
  `ℓ_h(π_v(1 ⊗ E_{pq}(c)) x) = i · [q = p + 1] aₚ c · ℓ_h(x)` with
  `aₚ = realWhittakerCoeff h v p`. The proof has four steps:
  - `π_v(1 ⊗ X)` is the Library's `S.lieOperator (realPlaceLieInclusion v X)` by definition.
  - `E_{pq}(c)` squares to zero.
  - `B E_{pq}(c) B⁻¹` is strictly upper triangular (`conj_single_apply_eq_zero`, with
    `isUpperTriangular_of_mul_eq_one` for `B⁻¹`).
  - `realizationFunctional_lieOperator` (Lemma C) applies, and the scalar is computed by
    the coordinate lemmas above.

  `realizationFunctional_complexPlaceLieAction_single` is the complex analogue.
- `operatorRealization_exists_evaluate_ne_zero`: a nonzero vector of an operator realization
  has a nonzero realized value, because `S.toContinuous` and `toContinuousMap` are injective.
  The prefix keeps the name distinct from the Library's
  `CuspidalWhittaker.exists_evaluate_ne_zero` for local realizations (module
  `CuspidalWhittaker.LocalFunctional`), which lives in the same namespace.
- `realizationFunctional_translate`: if `x'` is the right translate of `x` by `c`, then
  `ℓ_{g c⁻¹}(x') = W_x(g)`. This is the Library's `descend_mul_right`.
- `isRealGeneric_of_isStable` assembles the real case:
  - steps 1–2 of the outline, with Library `exists_upperTriangular_mul_unitary` applied to
    `realCoord v` of the archimedean component of `g₀`;
  - `k` the resulting orthogonal matrix, and `h₀ = g₀ · (k at v)⁻¹`;
  - the `v`-component of `h₀` is `b`, by the Library's `local_mul_inv`, `mul_inv_val_eq`
    and `realMatrix_realPlaceCompactInclusion`;
  - the witness is `S.realPlaceCompactRepresentation v k x₀ ∈ W` (stability), with
    `ℓ_{h₀}` of it equal to `W_{x₀}(g₀)` (`evaluate_realPlaceCompactRepresentation` and the
    previous lemma);
  - the coefficients are nonzero by `diag_mul_diag_eq_one`, and the Whittaker identity is
    `isRealWhittakerFunctional_of_single` with the per-unit identity.

  `isComplexGeneric_of_isStable` is the complex analogue, with `complexCoord v`, a unitary
  `k` and `complexMatrix_complexPlaceCompactInclusion`.
- `Langlands.Automorphic.cuspidalArchimedeanWhittakerFunctional` combines the two cases.

## Lean notes

The module uses `open scoped Classical` for decidable equality of places (as Mathlib's mixed
space and the Library's place inclusions do). It also declares local `AddCommGroup` instances
for the Library's function spaces, as `ArchimedeanFunctional` does. The per-unit identities
compute the scalar in a separate `have` and close the goal with `congrArg`. Rewriting directly
in goals containing `ℓ_h x` timed out.

## Sources

The mathematical argument is the infinitesimal form of the genericity of archimedean
components of cuspidal representations. A nonzero Whittaker coefficient gives a Whittaker
functional, and the Iwasawa decomposition moves the evaluation point so that the character
becomes the simple-root character twisted by the torus part `b` (Getz–Hahn,
`getz-hahn-2024-automorphic-representations`, (11.6) and Theorem 11.3.6, pp. 297–298, and
Exercise 11.3; cited in the Markdown of the target statement). The implemented proof is
self-contained given the Library results named above.
