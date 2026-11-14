# All-field port of `Langlands.Representation.GodementJacquet.TwoBlockReverseRealization`

`Langlands.AllField.Representation.GodementJacquet.TwoBlockReverseRealization` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.TwoBlockReverseRealization`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.TwoBlockReverseRealization` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Reverse realization of products of block zeta integrals**

Godement–Jacquet 1972, Theorem 3.4 (printed 43–45), for two blocks, by a direct
construction instead of Lemma 3.4.6: for block tests `Φ₀, Φ₁` and actual block
bi-smooth coefficients, a test `Φ` supported near the upper block-triangular
matrices and induced sections supported on `P K₀` realize a nonzero constant times
the product of the two block zeta integrals as an induced matrix zeta integral.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.TwoBlockZetaExpansion`

## Declarations

- `Langlands.AllField.GodementJacquet.TwoBlock.parabolicCompactSet` (def): The open set `P K₀` of products of an element of the upper two-block parabolic and
  an element of `K₀`.
- `Langlands.AllField.GodementJacquet.TwoBlock.isOpen_parabolicCompactSet` (theorem).
- `Langlands.AllField.GodementJacquet.TwoBlock.reverse_zeta_of_kernel` (theorem): **Reverse computation for a kernel supported on `P K₀`.** Let `K₀ ≤ K` be compact open
  subgroups, `ν` a finite measure on `K`, and `Γ` a continuous kernel on `K × GL_(t+1)` that
  vanishes for `k ∉ P K₀` and, for `k = q l` with `q ∈ P`, `l ∈ K₀`, is the left translate
  `y ↦ Γ₀ (q⁻¹ y)` of a continuous `Γ₀` supported on `P K₀` with
  `Γ₀ (parabolicPoint (L, x) l) = δ_P(L)^(1/2) c₀(a) c₁(d)`. For a test `Φ` invariant on both
  sides under `K₀` and an `s` at which all block tests converge against `c₀` and `c₁`, the
  coefficient `g ↦ ∫ k, Γ k (k g) dν` has convergent zeta integral at `s + t/2`, equal to an
  explicit constant times the Levi integral of `Φ^P`.
- `Langlands.AllField.GodementJacquet.TwoBlock.integralBox` (def): The compact open box of integral rectangular matrices.
- `Langlands.AllField.GodementJacquet.TwoBlock.isCompact_integralBox` (theorem).
- `Langlands.AllField.GodementJacquet.TwoBlock.isOpen_integralBox` (theorem).
- `Langlands.AllField.GodementJacquet.TwoBlock.zero_mem_integralBox` (theorem).
- `Langlands.AllField.GodementJacquet.TwoBlock.integralBoxTest` (def): The indicator of the integral box, a Schwartz–Bruhat function with value `1` at `0`.
- `Langlands.AllField.GodementJacquet.TwoBlock.integralBoxTest_apply` (theorem).
- `Langlands.AllField.GodementJacquet.TwoBlock.integralBoxTest_zero` (theorem).
- `Langlands.AllField.GodementJacquet.TwoBlock.blockSplit` (def): The four blocks `((A, D), B), C` of a matrix in the block convention.
- `Langlands.AllField.GodementJacquet.TwoBlock.blockJoin` (def): The matrix with prescribed blocks `((A, D), B), C`.
- `Langlands.AllField.GodementJacquet.TwoBlock.blockJoin_blockSplit` (theorem).
- `Langlands.AllField.GodementJacquet.TwoBlock.blockSplit_upper` (theorem).
- `Langlands.AllField.GodementJacquet.TwoBlock.continuous_blockSplit` (theorem).
- `Langlands.AllField.GodementJacquet.TwoBlock.continuous_blockJoin` (theorem).
- `Langlands.AllField.GodementJacquet.TwoBlock.reverseTest` (def): The test `X ↦ Φ₀(A) Φ₁(D) 1_box(B) 1_box(C)` for the blocks `[[A, B], [C, D]]` of `X`.
- `Langlands.AllField.GodementJacquet.TwoBlock.reverseTest_upper` (theorem).
- `Langlands.AllField.GodementJacquet.TwoBlock.upperBlockIntegral_reverseTest` (theorem): The upper-block integral of the reverse test is the product of the block tests.
- `Langlands.AllField.GodementJacquet.TwoBlock.exists_compactOpen_biInvariant` (theorem): A full-matrix test is invariant on both sides under some compact open subgroup
  contained in any prescribed open subgroup.
- `Langlands.AllField.GodementJacquet.TwoBlock.leviModulus_eq_one_of_mem` (theorem): The modulus of the upper two-block parabolic is trivial on elements of a compact
  subgroup.
- `Langlands.AllField.GodementJacquet.TwoBlock.exists_twoBlock_reverse_realization` (theorem): **Reverse realization.** For smooth admissible blocks, a block test and an actual
  bi-smooth block coefficient in each block, there are a full-matrix test, an actual
  bi-smooth coefficient of the induced representation and a nonzero constant `κ` such
  that, whenever the block integrals converge at `s + m₀/2` and `s + m₁/2`, the induced
  zeta integral converges at `s + t/2` and equals `κ` times the product of the two
  block zeta integrals.
- `Langlands.AllField.GodementJacquet.TwoBlock.twoBlock_reverse_generatorInput` (theorem): **Reverse generator input.** If both blocks satisfy the matrix analytic
  assertions, then the product of actual rational values of individual block zeta
  integrals lies in the Laurent span of the induced representation's values. This is
  the third component of `TwoBlockMatrixGeneratorInputs`.
- `Langlands.AllField.GodementJacquet.TwoBlock.twoBlock_matrixGeneratorInputs` (theorem): **Two-block generator inputs.** All three components of
  `TwoBlockMatrixGeneratorInputs` for the canonical normalized induced representation of
  two smooth admissible blocks satisfying the matrix analytic assertions.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.TwoBlock.smoothDualPairing_smoothContragredient`, `Langlands.GodementJacquet.TwoBlock.twoFamily`, `Langlands.GodementJacquet.TwoBlock.twoFamily_zero`, `Langlands.GodementJacquet.TwoBlock.twoFamily_one`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
