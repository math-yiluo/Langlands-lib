# All-field port of `Langlands.Representation.GodementJacquet.TwoBlockZetaExpansion`

`Langlands.AllField.Representation.GodementJacquet.TwoBlockZetaExpansion` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.TwoBlockZetaExpansion`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.TwoBlockZetaExpansion` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Finite product expansion of two-block induced matrix zeta integrals**

Godement–Jacquet 1972, Theorem 3.4 (printed 38–41), for two blocks: the shifted
matrix zeta integral of an actual bi-smooth coefficient of the normalized induced
representation is a finite sum of products of block matrix zeta integrals at the
block shifts, with data independent of `s`. Consequently the induced coefficients
converge on a common right half-plane and have rational values in the product of
the block Laurent spans.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.CompactProductCoefficients`
- `Langlands.AllField.Representation.GodementJacquet.TwoBlockSchwartz`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierInvariance`

## Declarations

- `Langlands.AllField.GodementJacquet.TwoBlock.halfModulus` (def): The complex half modulus `δ_P(L)^(1/2)` of the two-block Levi, as in the covariance
  law `normalizedProductInduced_covariant`.
- `Langlands.AllField.GodementJacquet.TwoBlock.blockAbs` (def): The real block determinant norm `|det (L i)|`.
- `Langlands.AllField.GodementJacquet.TwoBlock.blockAbs_pos` (theorem).
- `Langlands.AllField.GodementJacquet.TwoBlock.halfModulus_eq` (theorem): For two blocks, `δ_P(a, d) = |det a|^(n₁) / |det d|^(n₀)`.
- `Langlands.AllField.GodementJacquet.TwoBlock.normalizedAbs_det_eq_one_of_mem` (theorem): Elements of a compact subgroup have determinant of absolute value one.
- `Langlands.AllField.GodementJacquet.TwoBlock.determinantWeight_mul_of_mem` (theorem): The determinant weight is unchanged by two-sided translation by a compact subgroup.
- `Langlands.AllField.GodementJacquet.TwoBlock.levi_weight_identity` (theorem): **Levi weight identity.** In parabolic coordinates, the shifted determinant
  weight times `δ_P^(1/2)` and the radical factor is the product of the shifted block
  weights: `s + t/2` on `GL_(t+1)` becomes `s + m₀/2` and `s + m₁/2` on the blocks.
- `Langlands.AllField.GodementJacquet.TwoBlock.leviCoefficientWeight` (def): The Levi function `|det L|^(s + t/2) δ_P(L)^(1/2) c₀(a) c₁(d)` of a pair of block
  coefficients.
- `Langlands.AllField.GodementJacquet.TwoBlock.leviCoefficientWeight_mul` (theorem): Products of block test functions against the Levi weight are products of the
  block zeta integrands at `s + m₀/2` and `s + m₁/2`.
- `Langlands.AllField.GodementJacquet.TwoBlock.integrable_leviCoefficientWeight` (theorem): Integrability hypothesis of the parabolic reduction, from block convergence.
- `Langlands.AllField.GodementJacquet.TwoBlock.integral_leviCoefficientWeight` (theorem): The Levi integral of a product test function against the weight is a product of
  block zeta integrals.
- `Langlands.AllField.GodementJacquet.TwoBlock.continuous_leviCoefficientWeight` (theorem).
- `Langlands.AllField.GodementJacquet.TwoBlock.continuous_determinantWeight'` (theorem): Continuity of the shifted determinant weight on `GL_(n+1)`.
- `Langlands.AllField.GodementJacquet.TwoBlock.exists_zeta_expansion_of_kernel` (theorem): **Abstract two-block zeta expansion.** Let `K` be a compact open subgroup with
  `GL_(t+1) = P K`, `ν` a finite measure on `K`, and `Γ k y` a continuous kernel whose
  values on `parabolicPoint (L, x) * k'` expand as
  `δ_P(L)^(1/2) ∑ j, φ j (k, k') c₀ j (a) c₁ j (d)`. Then, for a full-matrix test `Φ`,
  there are finite data independent of `s` such that whenever every block test
  converges against the `c₀ j` at `s + m₀/2` and against the `c₁ j` at `s + m₁/2`, the
  matrix zeta integral of the coefficient `g ↦ ∫ k, Γ k (k g) dν` converges at
  `s + t/2` and equals `∑ i, w i Z₀(Ψ₀ i, c₀ (jj i)) Z₁(Ψ₁ i, c₁ (jj i))`.
- `Langlands.AllField.GodementJacquet.TwoBlock.exists_twoBlock_zeta_expansion` (theorem): **Forward expansion.** For smooth admissible blocks, a full-matrix test `Φ` and
  an actual bi-smooth coefficient of the normalized induced representation, there are
  finitely many block tests and actual block bi-smooth coefficients, chosen
  independently of `s`, such that whenever all block integrals converge at
  `s + m₀/2` and `s + m₁/2`, the induced zeta integral converges at `s + t/2` and is the
  corresponding finite sum of products of block zeta integrals.
- `Langlands.AllField.GodementJacquet.TwoBlock.twoBlock_forward_generatorInputs` (theorem): **Forward generator inputs.** If both blocks satisfy the matrix analytic
  assertions, then the actual bi-smooth coefficients of the induced representation
  converge on one common right half-plane, and each of their shifted zeta integrals
  has a rational value in the product of the two block Laurent spans.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.TwoBlock.weight_identity`, `Langlands.GodementJacquet.TwoBlock.normalizedAbs_det_pos`, `Langlands.GodementJacquet.TwoBlock.normalizedAbs_det_eq_blockAbs`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
