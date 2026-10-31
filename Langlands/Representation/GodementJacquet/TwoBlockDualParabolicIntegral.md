# The dual two-block parabolic integral

Module `Langlands.Representation.GodementJacquet.TwoBlockDualParabolicIntegral`.
Author: Worker 1117.

This module is a helper for the transformed side of the two-block functional
equation (Godement–Jacquet, *Zeta Functions of Simple Algebras* (1972), proof
of Theorem 3.4, printed 36–45). On the transformed side the zeta integral of
an induced representation is `∫ 𝓕Φ((g⁻¹)ᵀ) f(g) …`, with `𝓕Φ` the Fourier
transform of the test function. After the compact factors are split off, it is
an integral over the upper block parabolic in the coordinates
`(a, d, x) ↦ [[a, a x], [0, d]]`. Here `a` is in `GL_{n₀}`, `d` is in `GL_{n₁}`
and `x` is an `n₀ × n₁` matrix. The inverse transpose of this matrix is
`[[(a⁻¹)ᵀ, 0], [-(d⁻¹)ᵀ xᵀ, (d⁻¹)ᵀ]]`, so the radical variable enters through the
lower-left block. The substitution `C = -(d⁻¹)ᵀ xᵀ` multiplies the rectangular
Haar measure by `|det d|^(n₀)`. The lower-left partial integral of the test
function (Godement–Jacquet p. 38) then splits into the two Levi blocks.

The source does not state these lemmas separately. Their form comes from the
way the project organizes the two-block proof. The test function is
substituted along `g ↦ (g⁻¹)ᵀ`, and the same parabolic and compact data serve
both sides. The partial Fourier identity enters as the hypothesis `hpart`, a
finite tensor expansion of the lower-left partial integral.

Throughout, `blockMatrix e A B C D` is `Matrix.reindex e e (Matrix.fromBlocks A B C D)`
from `Langlands.HarmonicAnalysis.TwoBlockPartialFourier`, and
`rectangularMeasure ν r s` is the product of copies of the additive Haar measure
`ν` on `r × s` matrices. In the `Padic` namespace, `F` is a p-adic field with
its canonical topological data, the Borel measurable structure, and
`abv = normalizedAbsoluteValue F.canonicalTopologicalData`. These canonical
structures are installed as named local instances (`dualParabolicTopology`, …,
`dualParabolicGLBorelSpace`), so that the module can be imported together with the
modules that install the same structures anonymously in the same namespace.

## Transposition and block algebra (namespace `Langlands.GodementJacquet`)

- `measurable_matrix_transpose` and `transposeMeasurableEquiv r s` give the
  transpose `r × s → s × r` as a measurable equivalence, for any measurable
  space of entries.
- `measurePreserving_transpose_rectangularMeasure ν r s`: transposition carries
  `rectangularMeasure ν r s` to `rectangularMeasure ν s r` (for σ-finite `ν`).
  Proof: both sides are products of the same `r s` copies of `ν`. Equality is
  checked on measurable boxes with `Measure.pi_eq_generateFrom`, where the
  product over boxes is reordered by `Finset.prod_comm`.
- `inverseTranspose_val_of_upperBlock e g a d x hg`: over any commutative ring,
  if the matrix of `g` is `blockMatrix e a (a x) 0 d`, then the matrix of
  `(g⁻¹)ᵀ` is `blockMatrix e ((a⁻¹)ᵀ) 0 (-((d⁻¹)ᵀ xᵀ)) ((d⁻¹)ᵀ)`. Proof: the
  matrix `blockMatrix e a⁻¹ (-(x d⁻¹)) 0 d⁻¹` is a right inverse of `g` by
  block multiplication, so it is `g⁻¹`. Then transpose blockwise.

## Majorants

- `exists_isCompact_isClopen_superset`: in a locally compact Hausdorff totally
  disconnected space, every compact set lies in a compact clopen set. This is a
  finite union of the compact clopen neighbourhoods given by
  `HarmonicAnalysis.exists_compact_clopen`.
- `exists_blockMatrix_majorant e Φ`: for a Schwartz–Bruhat function `Φ` on
  `N × N` matrices over such a space `K` with a zero, there are a constant `M`
  and Schwartz–Bruhat functions `bA, bC, bD` on the three blocks with
  `‖Φ (blockMatrix e A 0 C D)‖ ≤ M (‖bA A‖ ‖bC C‖ ‖bD D‖)` for all `A, C, D`. The
  `b`'s are indicators of compact clopen sets that contain the projections of
  the support of `Φ` to the three blocks. `M` bounds `‖Φ‖`.

## Lower-left substitution (namespace `Langlands.GodementJacquet.Padic`)

- `mulLeftMeasurableEquiv F A s` is `X ↦ A X` on `r × s` matrices, as a
  measurable equivalence (from the homeomorphism with inverse `X ↦ A⁻¹ X`).
  `mulLeftMeasurableEquiv_apply` evaluates it.
- `map_mulLeftMeasurableEquiv`: the image of `rectangularMeasure ν r s` under
  `X ↦ A X` is `|det A|^(-s)` times `rectangularMeasure ν r s`, with
  `|det A|` the canonical determinant norm. This is the case `B = 1` of the
  published `padicRectangularHaarScaling`.
- `integral_comp_lowerLeft F ν d G`: for every function `G` on `n₁ × n₀`
  matrices with values in a real normed space,
  `∫ x, G (-((d⁻¹)ᵀ xᵀ)) d(rect n₀ n₁) = |det d|^(n₀) • ∫ C, G C d(rect n₁ n₀)`.
  Proof: transpose (measure preserving), then left multiplication by
  `A = -(d⁻¹)ᵀ`, for which `|det A| = |det d|⁻¹`.
- `integrable_comp_lowerLeft`: integrability transfers along the same
  substitution.

## The reduction

- `dualParabolicIntegrand F e Φ u0 u1 ((a, d), x)` is
  `Φ (blockMatrix e ((a⁻¹)ᵀ) 0 (-((d⁻¹)ᵀ xᵀ)) ((d⁻¹)ᵀ)) * u0 a * u1 d`, for
  `Φ` on `N × N` matrices, `e : Fin n₀ ⊕ Fin n₁ ≃ Fin N` and arbitrary functions
  `u0` on `GL_{n₀}` and `u1` on `GL_{n₁}`.
- `measurable_inverseTranspose_val n`: `a ↦ (a⁻¹)ᵀ` (as a matrix) is measurable
  on `GL_n`.
- `aestronglyMeasurable_dualParabolicIntegrand`: the integrand is a.e. strongly
  measurable for `(μ₀ × μ₁) × rect n₀ n₁`, whenever `u0` and `u1` are a.e.
  strongly measurable for the s-finite measures `μ₀` and `μ₁`.
- `integrable_integral_dualParabolicIntegrand F e ν Φ hu0m hu1m hu0 hu1 S α β
  hpart`: assume
  - `u0`, `u1` are a.e. strongly measurable;
  - for every Schwartz–Bruhat `Ψ`, `a ↦ Ψ((a⁻¹)ᵀ) u0(a)` is `μ₀`-integrable and
    `d ↦ Ψ((d⁻¹)ᵀ) (u1(d) |det d|^(n₀))` is `μ₁`-integrable;
  - `hpart`: for all `x, y`,
    `∫ C, Φ (blockMatrix e x 0 C y) d(rect n₁ n₀) = ∑ₖ∈S αₖ(x) βₖ(y)` with
    Schwartz–Bruhat `αₖ`, `βₖ`.

  Then `dualParabolicIntegrand F e Φ u0 u1` is integrable for
  `(μ₀ × μ₁) × rect n₀ n₁`, and its integral equals
  `∑ₖ∈S (∫ αₖ((a⁻¹)ᵀ) u0(a) dμ₀) (∫ βₖ((d⁻¹)ᵀ) (u1(d) |det d|^(n₀)) dμ₁)`.

  Proof. For fixed `(a, d)`, the `x`-integral is computed with
  `integral_comp_lowerLeft` and `hpart`. This gives
  `∑ₖ (αₖ((a⁻¹)ᵀ) u0(a)) (βₖ((d⁻¹)ᵀ) u1(d) |det d|^(n₀))`. For integrability on
  the product, `integrable_prod_iff` is used. Each fibre is integrable because
  `C ↦ Φ(blockMatrix e A 0 C D)` is dominated by `M ‖bA A‖ ‖bD D‖ ‖bC C‖`, and
  `bC` is integrable. The fibrewise integral of the norm is at most
  `M (∫ ‖bC‖) ‖bA((a⁻¹)ᵀ) u0(a)‖ ‖bD((d⁻¹)ᵀ) u1(d) |det d|^(n₀)‖`, which is
  integrable on `μ₀ × μ₁` by the hypotheses with `Ψ = bA` and `Ψ = bD`. The
  value then follows from Fubini (`integral_prod`), `integral_finsetSum`, and
  `integral_prod_mul`.
- `integrable_integral_dualParabolic_levi F e ν μ g hg Φ hu0m hu1m hu0 hu1 S α
  β hpart`: the same statement in Levi coordinates. Take
  `m : Fin 2 → ℕ`, `e : Fin (m₀+1) ⊕ Fin (m₁+1) ≃ Fin N`, and σ-finite measures
  `μ i` on `GL_{mᵢ+1}`. Take a map `g` from `(∀ i, GL_{mᵢ+1}) × M_{(m₀+1)×(m₁+1)}`
  to `GL_N` such that the matrix of `g (L, x)` is
  `reindex e e (fromBlocks L₀ (L₀ x) 0 L₁)`. Then
  `z ↦ Φ(((g z)⁻¹)ᵀ) (u0(L₀) u1(L₁))` (with `z = (L, x)`) is integrable for
  `(Measure.pi μ) × rect (m₀+1) (m₁+1)`. Its integral is
  `∑ₖ∈S (∫ αₖ((a⁻¹)ᵀ) u0(a) dμ₀) (∫ βₖ((d⁻¹)ᵀ) (u1(d) |det d|^(m₀+1)) dμ₁)`.
  The hypotheses on `u0, u1, α, β` are those above with `n₀ = m₀+1`,
  `n₁ = m₁+1`. Proof: `inverseTranspose_val_of_upperBlock` identifies the
  integrand with `dualParabolicIntegrand` composed with
  `(L, x) ↦ ((L₀, L₁), x)`. That map is a measure-preserving equivalence
  (`measurePreserving_piFinTwo` times the identity). For example, `g` can be
  `parabolicPoint h` with `e = blockEquiv h` and `μ i = generalLinearHaar F (m i)`,
  as in the two-block parabolic Haar module. Then the measure is that module's
  `parabolicMeasure` for the radical measure `rect (m₀+1) (m₁+1)`.

## Compact translates on the Fourier side

- `rectangularFourierEquiv_inverseTranspose_translate F ψ ν hsd A B hA hB Φ S c
  Φs hdec g`: take `A, B` in `GL_n(F)` with canonical determinant norm one. If
  `Φ (A x B) = ∑ₗ∈S cₗ Φₗ(x)` for all `x`, then for every `g`,
  `𝓕Φ(((A g B)⁻¹)ᵀ) = ∑ₗ∈S cₗ 𝓕Φₗ((g⁻¹)ᵀ)`. Here `𝓕` is
  `rectangularFourierEquiv ψ ν n n hsd` and `A g B` is written `A * (g * B)`.
  Proof: the inverse transpose is multiplicative, and
  `rectangularFourierIntegral_translate_decomposition` (module
  `Langlands.HarmonicAnalysis.RectangularFourierUnimodularTranslate`) applies at
  `y = (g⁻¹)ᵀ`.
- `rectangularFourierEquiv_inverseTranspose_translate_of_mem`: the same
  conclusion when `A` and `B` lie in a compact subgroup `K` of `GL_n(F)`. Such
  elements have determinant norm one (`PadicField.TopologicalData.determinantNorm_eq_one_of_mem_compact`).
  This is the form needed on the transformed side when the compact factors
  `A = (j k)⁻¹` and `B = j' k'` are split off.

## Scope

The module proves no partial Fourier identity: `hpart` is a hypothesis. In
the two-block proof it is supplied by
`integral_rectangularFourierIntegral_blockMatrix_lowerLeft_of_tensor`
(module `Langlands.HarmonicAnalysis.TwoBlockPartialFourier`) for a Fourier
transform `𝓕Φ`. The weights `u0`, `u1` are arbitrary a.e. strongly
measurable functions subject only to the stated integrability; no
representation theory, coefficient formula or zeta-integral shift appears
here. The exponents that turn the right-hand side into block zeta integrals
are matched in the consumer module. The Levi-coordinate form needs only the
matrix identity `hg` for `g`, not the group law of the parabolic subgroup.
