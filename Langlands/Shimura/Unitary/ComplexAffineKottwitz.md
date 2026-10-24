# Affine Kottwitz cocharacters and embedding weight spaces

This internal construction connects the existing Kottwitz cocharacter to the actual embedding-labelled matrices of its evaluated rational-group points. It derives from `ComplexKottwitzMatrices`, `ComplexAffineCocharacterComparison`, `CMEmbeddingIndices`, and `ComplexWeightSpaces`. It uses their constructed maps and their established matrix and rank formulas; neither the new coordinate comparison nor the new rank equality is an input assumption.

The generic helper `Gm.relativeAffineUnitPoint_inverse_sections` works for every commutative algebra `T` over a commutative ring `R`, in any universe. The canonical affine section normalization sends the inverse global unit of the relative affine point associated to `u : Tˣ` to `u⁻¹`. Its proof first lifts the existing equality on unit values to an equality of units and then applies preservation of inversion by the induced homomorphism on units.

For the actual central-simple unitary datum `D` and Harris signature charts `C`, `kottwitzCocharacter_affine_matrices` computes the matrices of the relative affine value of either Kottwitz cocharacter. Here `T` is a commutative complex algebra in `Type`, equipped with a compatible real algebra structure. At a real place `τ`, put `r = n - 1` if `τ` is distinguished, and `r = n` otherwise. The result is `ComplexMatrix.splitDiagonal T n r` evaluated on `(1,u⁻¹)` for the first cocharacter and on `(u⁻¹,1)` for the second. The proof applies the existing matrix formula on global sections, the entrywise normalization formula for split diagonal matrices, and the inverse-unit helper. In particular it retains conjugation before inversion in the Kottwitz convention.

For a compatible CM section proof `hΦ`, `kottwitzCocharacter_embedding_matrices` computes the matrix of the actual rational-group point `D.complexCocharacterValue (D.kottwitzCocharacter C first) u` at `cmFactorEmbedding Φ (τ,b)`. It is the first matrix of that same split diagonal when `b = true`, and the second when `b = false`. Thus `true` labels the chosen embedding `Φ τ` and `false` its complex conjugate. The proof uses the canonical relative-affine to rational evaluation comparison and the existing embedding-coordinate comparison, followed by the preceding affine formula at `T = ℂ`.

`D.kottwitzEmbeddingWeightSpace C hΦ i` is a complex vector subspace of `Fin n → ℂ`. Its elements are exactly the vectors `v` satisfying

\[
 M_i(u)v = u^{-1}v \quad\text{for every }u\in\mathbf C^\times,
\]

where `M_i(u)` is the matrix at the CM embedding `i` of the actual rational point obtained by evaluating the first Kottwitz cocharacter at `u`. This is an application of the existing common inverse-weight submodule construction, with no coordinate support or dimension built into the definition.

`kottwitzEmbeddingWeightSpace_diagonal` identifies this subspace at `(τ,b)` with the inverse-weight space of the diagonal family whose support is `j < r` for `b = true`, and `j ≥ r` for `b = false`. Its proof substitutes the actual embedding matrix formula and separates the two Boolean cases. `finrank_kottwitzEmbeddingWeightSpace_factor` then applies the existing diagonal rank theorem and counts these coordinates. The chosen embedding has rank `n - 1` at the distinguished place and `n` elsewhere; the conjugate embedding has rank `1` at the distinguished place and `0` elsewhere. The complementary count uses the chart assumption `n > 1`.

Finally, `finrank_kottwitzEmbeddingWeightSpace` proves for every `i : K →+* ℂ` that

\[
 \dim_{\mathbf C}\bigl(D.\mathrm{kottwitzEmbeddingWeightSpace}(C,h_\Phi,i)\bigr)
   = D.\mathrm{realHodgeFunction}(C,i).
\]

The proof expresses `i` through the bijection `cmFactorEmbeddingEquiv Φ hΦ`, applies the factor rank calculation, and uses the established real Hodge function formula. The inverse bijection's Boolean records precisely whether `i` is the selected embedding above its real place, so the two case distinctions agree.

All number-field, central-simple algebra, involution, scalar-tower, and signature assumptions are inherited from the existing actual constructions. This module identifies numerical Hodge data with weight spaces of evaluated cocharacters. It does not prove Galois invariance of those dimensions, innerness of chart changes, conjugacy of transported scheme cocharacters, or equality with a scheme-cocharacter reflex field. Smoothness, reductivity, Shimura levels, and coefficient descent also remain separate obligations.
