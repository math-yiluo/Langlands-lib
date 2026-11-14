# All-field port of `Langlands.Representation.GodementJacquet.TwoBlockMatchedZetaExpansion`

`Langlands.AllField.Representation.GodementJacquet.TwoBlockMatchedZetaExpansion` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.TwoBlockMatchedZetaExpansion`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.TwoBlockMatchedZetaExpansion` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Matched expansion of two-block induced zeta integrals and their transforms**

Godement–Jacquet 1972, proof of Theorem 3.4 (printed pages 37–42), for two blocks:
the shifted matrix zeta integral of a bi-smooth coefficient `f` of the normalized
induced representation is a finite sum of products of block zeta integrals, and,
with the same finite data, the zeta integral of the full Fourier transform of the
test against the inverse-transpose transform of `f` is the corresponding sum of
products of the block zeta integrals of the Fourier transforms of the block tests
against the inverse-transpose transforms of the block coefficients. This proves
`TwoBlockMatchedZetaExpansionStatement`. See the paired Markdown.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.InverseTransposeMatrixIntegral`
- `Langlands.AllField.Representation.GodementJacquet.TwoBlockDualParabolicIntegral`
- `Langlands.AllField.Representation.GodementJacquet.TwoBlockFunctionalEquationAssembly`
- `Langlands.AllField.Representation.GodementJacquet.TwoBlockZetaExpansion`

## Declarations

- `Langlands.AllField.GodementJacquet.TwoBlock.dual_levi_weight_identity` (theorem): **Transformed Levi weight identity.** In parabolic coordinates, the determinant
  weight with exponent `-(s + t/2)` times `δ_P^(1/2)` is the product of the block
  weights with exponents `-(s + m₀/2)` and `-(s + m₁/2) - n₀`.
- `Langlands.AllField.GodementJacquet.TwoBlock.determinantWeight_sub_natCast_mul_pow` (theorem): Lowering the exponent by `k` and multiplying by `|det g|^k` restores the weight.
- `Langlands.AllField.GodementJacquet.TwoBlock.exists_matched_zeta_expansion_of_kernel` (theorem): **Matched abstract two-block zeta expansion.** In the setting of
  `exists_zeta_expansion_of_kernel`, with the radical measure taken to be the
  rectangular product of a measure `ν` self-dual for `ψ`, one finite family of
  weights, block tests and coefficient indices expands both the zeta integral of
  the coefficient `f g = ∫ k, Γ k (k g) dμK` against `Φ`, and the zeta integral of the
  inverse-transpose transform `ι f` against the full Fourier transform of `Φ`; in
  the second expansion the block tests are replaced by their Fourier transforms and
  the block coefficients by their inverse-transpose transforms. Each identity holds
  whenever the corresponding block integrals converge.
- `Langlands.AllField.GodementJacquet.TwoBlock.exists_twoBlock_matched_zeta_expansion` (theorem): **Matched forward expansion.** For smooth admissible blocks, a full-matrix test
  `Φ` and a coefficient `f = ⟨ℓ, I(g) v⟩` of the normalized induced representation
  `I`, there are finitely many weights, block tests and actual block bi-smooth
  coefficients, chosen independently of `s`, such that: whenever all block integrals
  converge at `s + m₀/2` and `s + m₁/2`, the zeta integral of `f` against `Φ` at
  `s + t/2` is the weighted sum of products of the block zeta integrals; and whenever
  all inverse-transpose block integrals converge there, the zeta integral of `ι f`
  against the full Fourier transform of `Φ` is the same weighted sum with Fourier
  transformed block tests and inverse-transpose block coefficients.
- `Langlands.AllField.GodementJacquet.TwoBlock.padic_matrixIntegral_smul` (theorem): Scalars pull out of the canonical p-adic matrix integral.
- `Langlands.AllField.GodementJacquet.twoBlockMatchedZetaExpansion` (theorem): **Matched expansion.** The internal interface `TwoBlockMatchedZetaExpansionStatement`
  holds: the matched forward expansion, with the weights absorbed into the first
  block coefficients, reindexed by `Fin M`, on the common convergence half-planes of
  the block data.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.TwoBlock.dual_weight_identity`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
