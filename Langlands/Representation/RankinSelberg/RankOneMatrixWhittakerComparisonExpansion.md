# Matrix integrals of a Whittaker model as rank-one integrals

Module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonExpansion`,
namespace `Langlands.RankinSelberg.RankOneIwasawa`. It proves the inclusion
"Right ⊆ Left" of the positive-rank branch (`n = m + 1`, actual rank `m + 2`) of
`RankOneMatrixWhittakerComparisonStatement`.

## Main results

Let `F` be a canonical `p`-adic field, `ψ` a nontrivial unitary additive character, `σ` a
smooth representation of `GL_(m+2)(F)` on an arbitrary complex vector space, and `ℓ` a
standard Whittaker functional.

- `exists_rankOneModel_of_matrix`: for each matrix test function `Φ` and model vector
  `w`, there is one model vector `w'` with the following property for every `s`. If the
  shifted matrix integrand `Φ(y) W(y) |det y|^(s + (m+1)/2)` is integrable for
  `generalLinearHaar F (m+1)`, then the rank-one integrand
  `W'(diag(det g, 1, …, 1)) |det g|^(s - (m+1)/2)` (`rankOneModelIntegrand`) is integrable
  for `generalLinearHaar F 0`, and the two integrals are equal. The vector `w'` does not
  depend on `s`.
- `whittakerRationalValues_subset_rankOneModelValues`:
  `GodementJacquet.Padic.whittakerRationalValues F ψ σ ℓ ⊆ rankOneModelValues q ψ abv
  (generalLinearHaar F 0) σ ℓ`, with the canonical residue cardinality `q` and absolute
  value. A convergence half-plane and a rational continuation of the matrix integral
  give the same for `Ψ(s, W')`, on the larger of the two half-planes.

Only smoothness of `σ` is used. Admissibility, finite generation and the
multiplicity-one part of `IsOfWhittakerType` are not used here.

## Proof

1. **Unfolding** (`RankOneMatrixUnfolding.integral_matrixIntegrand_unfold`). The matrix
   integral equals `∫ J(D(g,a)k) W(D(g,a)k) |det|^(s + (m+1)/2)` over
   `|det g|⁻ⁿ dg × ω(1,a) da × dk|_K`, and this integrand is integrable.
2. **The family.** `hProduct y = J(y) W(y)`, and
   `hFamily (a, k) = (g ↦ 1_K(k) · J(D(g,a)k) W(D(g,a)k))`. Almost everywhere, the
   unfolded integrand is `hFamily (a,k) g · |det g|^(s + (m+1)/2)`
   (`ae_outerMeasure_mem`, `determinantWeight_diagPoint`).
3. **Finitely many values** (`hFamily_finite`).
   - Right invariance. `W` is right invariant under a congruence subgroup
     (`exists_model_congruence`, from `model_isSmooth` and `exists_congruenceGroup_le`),
     and so is `Φ` (`exists_schwartz_congruence`); hence so is `hProduct`. Right
     translation of `(a, k)` by `(ε, κ)` in `(U_M)ⁿ × K_M` (`unitsCongruence`,
     `outerCongruence`) changes `D(g,a)k` by the congruence element
     `k⁻¹ D(1,ε) k κ` (`diagPoint_mul`, `diagonalUnits_mem_congruenceGroup`,
     `conj_mem_congruenceGroup`). So `hFamily` is locally constant (Worker 902's
     `isLocallyConstant_of_mul_right_invariant`).
   - Compact support. By `unipotentTransform_diag_bounds`, `hFamily` vanishes unless
     every `aᵢ` and `aᵢ⁻¹` lies in fixed lattices and `k` is integral. That set is
     compact (`isCompact_unitBox` via `Units.isClosedEmbedding_embedProduct`, and
     `isCompact_integralSet`).
   - Worker 902's `finite_range_of_isLocallyConstant` then gives finitely many values,
     with measurable fibres.
4. **Each value is a model function on the embedded `GL₁`** (`exists_model_hFamily`).
   For integral `k`, `J(D(g,a)k) = φ(det g)` for a Schwartz–Bruhat function `φ`. This is
   `exists_cornerSchwartz` composed with multiplication by `(∏ a)⁻¹`. Also
   `D(g,a)k = diag(det g, 1, …, 1) · t · k` with `t = diag((∏ a)⁻¹, a)`, so
   `W(D(g,a)k)` is the right translate of `W` by `t k` on the embedded `GL₁`. Worker
   902's Fourier cutoff `exists_rankOneCutoff` gives a model vector whose function on
   `diag(det g, 1, …, 1)` is `φ(det g)` times that translate.
5. **Level-set expansion** (Worker 902's `integral_prod_eq_sum_levelSets`). The
   integral is `Σ_v ν(fibre of v) · ∫ v(g) |det g|^(s+(m+1)/2) |det g|⁻ⁿ dg`. The
   density identity `weight_smul_determinantWeight` gives the exponent `s - (m+1)/2`.
   So `w' = Σ_v ν(fibre of v) · w_v`, using linearity (`glModelFunction_sum`).
6. **Convergence.** A fibre of positive measure makes `v(g) |det g|^(s+(m+1)/2)`
   integrable for `|det g|⁻ⁿ dg` (Worker 902's `integrable_of_integrable_prod_levelSet`).
   The terms with fibre of measure zero have coefficient zero.

## Provenance

This is the comparison of the Godement–Jacquet integral with the JPSS integral
`Ψ(s, W)` for the trivial character of `GL₁`, following Jacquet–Piatetski-Shapiro–Shalika
(1979), Section 4 (Remark 4.2, Theorem 4.3), as invoked in JPSS (1983), Section 5.2. The
proof route here is internal: Iwasawa unfolding, support bounds proved by translation,
a finite level-set expansion and a Fourier cutoff. It is not a transcription of the
original argument.
