# Positive forms from Zariski-dense compact subgroups

This module is an internal derivation. It combines Mathlib's Haar measure and
Bochner integral with the published `AlgebraicMatrixPowers`,
`MatrixRepresentationPolynomialImage` and `InfinitePlaceMatrixRealization`
modules, and with the positive-form normalization in
`MatrixRepresentationPositiveForm`. The averaging step is the classical
unitary-trick construction of an invariant inner product for a compact group.
Stability of the whole group under the form adjoint is derived here from a
polynomial-density hypothesis, by transferring polynomial equations. The
module asserts no literature identification. It does not show that the
density hypothesis holds for any particular reductive group.

Throughout, the scalar field `𝕜` (or `k`) is an arbitrary `RCLike` field and
the index type `n : Type` is finite with decidable equality; it may be empty.
Star on matrices and on `GL n 𝕜` is conjugate transpose. The order on `𝕜`
used for positivity is the `ComplexOrder` scope, as in the published polar
modules.

## Averaging (namespace `Langlands.Group.DenseCompactForm`)

Let `K : Type v` be a group and `φ : K →* GL n 𝕜` a homomorphism. The matrix
`pulledForm φ k` is `star (φ k)⁻¹ * (φ k)⁻¹`, the standard Hermitian form
pulled back along `(φ k)⁻¹`. For a measure `μ` on `K`,
`averagedForm μ φ` is the Bochner integral of `pulledForm φ` against `μ`. The
integral uses Mathlib's entrywise supremum norm on matrices
(`Matrix.normedAddCommGroup`, `Matrix.normedSpace`), enabled as local
instances; it induces the usual matrix topology.

- `pulledForm_mul_left` computes the pulled form at `h⁻¹ * k` as
  `star (φ h) * pulledForm φ k * φ h`.
- `dotProduct_pulledForm` writes `x* (pulledForm φ k) x` as the real number
  `∑ i ‖((φ k)⁻¹ x) i‖²`, cast to `𝕜`.
- If `K` carries a topology and `φ` is continuous, then `pulledForm φ` is
  continuous (`continuous_pulledForm`). If moreover `K` is compact with a
  Borel σ-algebra and `μ` is a finite measure, then `pulledForm φ` is
  integrable (`integrable_pulledForm`).
- `star_mul_averagedForm_mul`: suppose in addition that `K` is a
  topological group and `μ` is left invariant. Then
  `star (φ h) * averagedForm μ φ * φ h = averagedForm μ φ` for every `h`. The proof moves left and right multiplication inside the
  integral as a continuous linear map and applies
  `pulledForm_mul_left`. Left invariance of `μ` then absorbs the translation
  by `h⁻¹`.
- `isHermitian_averagedForm` needs only the integrability hypotheses.
  Conjugate transpose is a continuous
  conjugate-linear map, so it commutes with the integral. Each pulled form is
  Hermitian.
- `posDef_averagedForm`: suppose, with the integrability hypotheses, that
  `μ` is positive on nonempty open sets. Then the averaged form is positive definite. For
  `x ≠ 0` the quadratic form is the integral of the continuous nonnegative
  function `k ↦ ∑ i ‖((φ k)⁻¹ x) i‖²`, which is nonzero at `k = 1`. Hence the
  integral is strictly positive.

`exists_posDef_invariant` applies this to a subgroup `K₀` of `GL n 𝕜` that is
compact in the matrix topology. It takes the Haar measure on `K₀` with the
Borel σ-algebra and the inclusion homomorphism. The result is `J : GL n 𝕜`
with `J` positive definite and `star k * J * k = J` for every `k ∈ K₀`.

## Polynomial transfer

The coordinates `Coordinate n` and evaluations `values g` are the published
matrix-entry and inverse-matrix-entry coordinates of `GL n 𝕜`. For
`J : GL n 𝕜`, `adjointCoordinate J` gives, for each coordinate, a linear
polynomial with conjugated coefficients. Evaluated at `values g`, it gives the
complex conjugate of the corresponding coordinate of the form adjoint
`J⁻¹ * star g * J` (`eval_adjointCoordinate`). For inverse entries this uses
`(J⁻¹ * star g * J)⁻¹ = J⁻¹ * star g⁻¹ * J`. Next, `adjointPolynomial J p`
conjugates the coefficients of `p` and substitutes these linear polynomials.
`eval_adjointPolynomial` states that its value at `values g` is the conjugate
of the value of `p` at the form adjoint of `g`.

`formAdjoint_mem_of_dense` takes subgroups `K₀ ≤ A` of `GL n 𝕜` with the
following properties.

1. `A` is polynomially defined in the published sense
   `IsPolynomiallyDefined`.
2. Every polynomial in `MvPolynomial (Coordinate n) 𝕜` that vanishes on
   `values k` for all `k ∈ K₀` also vanishes on `values g` for all `g ∈ A`.
   This is Zariski density of `K₀` in `A`, with polynomial coefficients in
   `𝕜`.
3. `J` satisfies `star k * J * k = J` for all `k ∈ K₀`.

Then `J⁻¹ * star g * J ∈ A` for every `g ∈ A`. Here is the proof. For a
defining equation `p` of `A`, the polynomial `adjointPolynomial J p` vanishes
on `K₀`. This holds because the form adjoint of `k ∈ K₀` is `k⁻¹ ∈ A`. By
density it vanishes on `A`, so `p` vanishes at the form adjoint of every
`g ∈ A`.

`exists_posDef_formAdjoint_of_dense` combines both steps. Suppose `K₀` is
compact, `A` is polynomially defined and `K₀` is dense in `A` as above. Then
there is a positive definite `J` that is invariant under `K₀` and whose form
adjoint preserves `A`.

## Actual representations (namespace `Langlands.GroupScheme.MatrixRepresentation`)

Let `G` be an actual group scheme over `Spec k` whose underlying scheme is
affine, and let `ρ : MatrixRepresentation G n` be a closed subgroup
representation (`IsClosedSubgroup ρ`). The actual base-field points
`G.affinePoints (CommAlgCat.of k k)` carry the existing regular-function
evaluation topology `G.affinePointsTopologicalSpace`, installed as a local
instance.

`exists_closed_starStable_of_denseCompact` takes a subgroup `K₀` of these
actual points that is compact in this topology. It assumes the density
hypothesis in coefficient form: every polynomial in
`MvPolynomial (Coordinate n) k` that vanishes on `values (ρ(x))` for all
`x ∈ K₀` vanishes on `values (ρ(x))` for every actual point `x`. Here `ρ` is
the actual coefficient homomorphism `ρ.affineMatrix (CommAlgCat.of k k)`. The
theorem produces an actual representation `σ : MatrixRepresentation G n` with
four properties:

- `σ` is again a closed subgroup representation;
- its actual coefficient map is a closed embedding for the evaluation
  topology;
- its actual coefficient image is stable under conjugate transpose;
- `σ(x)` is a unitary matrix for every `x ∈ K₀`.

Here is the proof. The image `ρ(K₀)` is compact, by continuity of the
published closed embedding `isClosedEmbedding_affineMatrix`. The full image
`(ρ.affineMatrix (CommAlgCat.of k k)).range` is polynomially defined by the
published `affineMatrix_range_isPolynomiallyDefined`. The hypothesis is
exactly the density premise for `ρ(K₀)` in this range. Therefore
`exists_posDef_formAdjoint_of_dense` supplies `J`, and `σ` is
`ρ.positiveFormConjugate J hJ`. Its closedness, closed embedding and adjoint
stability come from `MatrixRepresentationPositiveForm` and
`InfinitePlaceMatrixRealization`. For unitarity, write `C` for the Hermitian
square root of `J` and `g = ρ(x)`. The new matrix is `C g C⁻¹`, and
`(C g C⁻¹)* (C g C⁻¹) = C⁻¹ (g* J g) C⁻¹ = C⁻¹ J C⁻¹ = 1`.

## Scope

The compact subgroup and its Zariski density are explicit premises. Over
`k = ℝ` a compact subgroup is usually not Zariski dense in the real points of
a noncompact group. The real case therefore needs a separate passage through
complex points, which is not done here. This module does not construct
compact real forms or relate geometric reductivity to them. It does not
compare actual parabolics with cocharacter parabolics or prove the host
`InfinitePlaceGroupPoints.ParabolicIwasawaStatement`. Those remain separate
obligations of the full local existence proof.
