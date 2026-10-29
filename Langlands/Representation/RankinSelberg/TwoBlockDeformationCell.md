# The upper radical of the lower two-block induction

Module `Langlands.Representation.RankinSelberg.TwoBlockDeformationCell`,
namespace `Langlands.RankinSelberg.TwoBlockDeformation`.

Author: Worker 831.

This is a helper module for the proof of
`Langlands.RankinSelberg.TwoBlockWhittakerDeformationStatement` (JPSS 1983,
Section (4.5)). It records how upper unipotent translation acts on the
restriction of a section to the upper radical, and the consequences for the
integral of JPSS (4.6.2) at the identity. The module proves no convergence for
general sections, no analytic statement in a parameter `u`, and no
nonvanishing.

## Provenance

JPSS (source ID `jpss-1983-rankin-selberg`), Section 4.6, printed pages
410–411, define the integral (4.6.2) over `x ∈ M(t₁ × t₂)` of
`f((1 x; 0 1) g; e, e) θ((1 x; 0 1))` for the lower block parabolic. The
block factorization below and the change of variables are the standard
computation showing that this integral at the identity transforms under
upper unipotent translation by the inverse standard character `θ⁻¹`. They are
internal content of this proof; the source does not state them as numbered
results.

The setting is that of the published
`Langlands.Representation.RankinSelberg.TwoBlockJacquetData`: `F` is a
`p`-adic field, `B = succBlockShape m h` with `h : ∑ i, (m i + 1) = t + 1`,
the blocks have ranks `m 0 + 1` and `m 1 + 1`, `σ i` are arbitrary complex
representations on `W i`, `Sections F h σ` is the space of the lower
normalized induction, `upperRadical h R x = (1 x; 0 1)`, and
`jacquetFunction ψ ell μ f g` is the Bochner integral of
`x ↦ ⟨f(u(x) g), ⊗ ell i⟩ ψ(x_(m 0, 0))` against a supplied measure `μ`.

## Matrix identities (section `Matrix`, any commutative ring `R`)

- `val_index_zero`, `val_index_one`: the block coordinate `index 0 a` has
  value `a`, and `index 1 b` has value `m 0 + 1 + b`.
- `sum_index`: a sum over `Fin (t + 1)` splits into the sums over the two
  blocks.
- `mul_apply_index`: a matrix product entry, written as the two block sums.
- `ext_index`: two elements of `GeneralLinear (t + 1) R` are equal if their
  four blocks agree.
- `leviEmbedding_index_zero_one`, `leviEmbedding_index_one_zero` (simp): the
  off-diagonal blocks of a Levi element vanish.
- `upperUnipotent_index_one_zero`: the lower-left block of an upper unipotent
  matrix vanishes.
- Section `BlockSums`: rewriting lemmas for sums of products against blocks of
  `upperRadical h R x`, of a Levi element and of an upper unipotent matrix
  (`sum_radical_zero_zero_mul`, `sum_mul_radical_zero_zero`,
  `sum_radical_one_one_mul`, `sum_mul_radical_one_one`,
  `sum_radical_zero_one_mul`, `sum_mul_radical_zero_one`,
  `sum_radical_one_zero_mul`, `sum_mul_radical_one_zero`,
  `sum_levi_zero_one_mul`, `sum_levi_one_zero_mul`,
  `sum_mul_unipotent_one_zero`). They are proved with `rw` on the published
  `upperRadical_index_*` lemmas.
- `unipotentLevi h n`: the Levi element `(n_0, n_1)` of diagonal blocks of an
  upper unipotent `n`, defined as the Levi projection of `n` viewed in the
  upper block parabolic. `unipotentLevi_apply` (simp) gives its entries, and
  `unipotentLevi_mem` shows that each block is upper unipotent.
- `unipotentCorner h n`: the upper-right block `β` of `n`.
- `unipotentShift h n x = n_0⁻¹ (β + x n_1)`.
- `upperRadical_mul_upperUnipotent`: the block factorization
  `u(x) n = diag(n_0, n_1) u(n_0⁻¹ (β + x n_1))`. It is checked block by
  block with `ext_index`.
- `sum_superdiagonal_index`: the sum of the first superdiagonal of a
  `(t + 1) × (t + 1)` matrix is the superdiagonal sum of block `0`, plus the
  corner entry at `(index 0 (last), index 1 0)`, plus the superdiagonal sum of
  block `1`.
- `upperUnipotent_mul_apply_last`, `mul_upperUnipotent_apply_zero`: the last
  row of an upper unipotent `A` is the last unit row, and the first column of
  an upper unipotent `C` is the first unit column, so `(A x)_(last, j) =
  x_(last, j)` and `(x C)_(i, 0) = x_(i, 0)`.
- `unipotentShift_last_zero`: the corner coordinate of the shift is
  `β_(m 0, 0) + x_(m 0, 0)`.

## Sections (section `Sections`)

- `determinantNorm_eq_one_of_mem_upperUnipotent`: an upper unipotent matrix
  has determinant `1`, hence determinant norm `1` for every topological datum.
- `leviModulus_eq_one`: the block modulus is `1` on a Levi element whose
  blocks have determinant norm `1`.
- `sectionEval_leviEmbedding_mul`: for such a Levi element `L`,
  `f(L g) = (σ_0 ⊗ σ_1)(L) f(g)`. This is the published covariance
  `normalizedOppositeParabolicInduced_covariant` with trivial modulus.
- `radicalRestriction F h σ f x = f(u(x))`.
- `radicalRestriction_inducedRep`: for `n` upper unipotent,
  `(ρ(n) f)(u(x)) = (σ_0 ⊗ σ_1)(n_0, n_1) f(u(n_0⁻¹ (β + x n_1)))`, from
  the block factorization.
- `compactRadicalSubmodule F h σ`: the complex subspace of sections whose
  radical restriction has compact support (canonical topology).
  `mem_compactRadicalSubmodule` unfolds membership.
- `inducedRep_mem_compactRadicalSubmodule`: this subspace is stable under the
  upper unipotent group. The radical restriction of `ρ(n) f` is a linear map
  composed with the radical restriction of `f` and the homeomorphism
  `x ↦ n_0⁻¹ (β + x n_1)` (the published `affineHomeomorph`).

## Contraction and character (section `Contraction`)

Here `ψ` is a unitary additive character and `ell i : W i →ₗ[ℂ] ℂ`.

- `tensorContraction_blockTensor`: if each `ell i` lies in
  `glInverseFunctionals ψ (m i) (σ i)` and each block of `L` is upper
  unipotent, then contracting `(σ_0 ⊗ σ_1)(L) v` with `⊗ ell i` gives
  `∏ i θ_i⁻¹(L i)` times the contraction of `v`. Proved on pure tensors by
  `PiTensorProduct.induction_on`.
- `inverseStandardCharacter_eq_prod`: for `n` upper unipotent of rank
  `t + 1`, `θ⁻¹(n) = θ_0⁻¹(n_0) θ_1⁻¹(n_1) ψ(β_(m 0, 0))⁻¹`, from
  `sum_superdiagonal_index`.

## The integral at the identity (section `Jacquet`)

These results assume measurable addition and multiplication on `F.Carrier`
where needed, a Borel structure on the rectangular matrices, and an additive
Haar measure `μ`.

- `integral_comp_unipotentShift`: `∫ G(n_0⁻¹ (β + x n_1)) dμ = ∫ G dμ` for
  every `G` and every upper unipotent `n`. The map is a translation composed
  with the published `Shahidi.rectangularConj n_0 n_1`. By
  `Shahidi.map_rectangularConj_padic` the latter scales `μ` by
  `|det n_0|^(m 1 + 1) / |det n_1|^(m 0 + 1) = 1`, and additive Haar measures
  are translation invariant.
- `jacquetFunction_inducedRep_upperUnipotent`: if each `ell i` lies in
  `glInverseFunctionals ψ (m i) (σ i)`, then for **every** section `f` and
  every upper unipotent `n`,
  `jacquetFunction ψ ell μ (ρ(n) f) 1 = θ⁻¹(n) · jacquetFunction ψ ell μ f 1`.
  The integrand of `ρ(n) f` at `x` equals `θ⁻¹(n)` times the integrand of `f`
  at `n_0⁻¹ (β + x n_1)`, by `radicalRestriction_inducedRep`,
  `tensorContraction_blockTensor`, `unipotentShift_last_zero` and
  `inverseStandardCharacter_eq_prod`. Then `integral_comp_unipotentShift`
  applies. No integrability is used: the Bochner integral is invariant under
  the measure-preserving change of variables whether or not the integrand is
  integrable.
- `isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule`: for a measure that
  is finite on compact sets (on an opens-measurable space), every section in
  `compactRadicalSubmodule` satisfies `IsAbsIntegrableAt ψ ell μ f 1`. The
  integrand is continuous (sections are locally constant) with compact
  support.
- `compactRadicalJacquet F h σ ψ ell μ hint`: the linear functional
  `f ↦ jacquetFunction ψ ell μ f 1` on `compactRadicalSubmodule`, given a
  proof `hint` of integrability on that subspace (additivity of the Bochner
  integral needs it). `compactRadicalJacquet_apply` unfolds it.
- `compactRadicalJacquet_inducedRep`: this functional is
  `θ⁻¹`-equivariant under the upper unipotent group, as a consequence of
  `jacquetFunction_inducedRep_upperUnipotent`.
