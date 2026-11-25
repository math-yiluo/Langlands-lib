# The Leray splitting factor of `U(ν, ν)` on every Bruhat cell

**GKT §11.2** (§11.2.1, the Rao function, p. 317; **(11.3)** and **Theorem 11.6**, p. 318), in Case
`3₊` with `W` split, for the Weil representation `lerayWeil c ν ψ χ Q` of `U(ν, ν)` of
`Langlands.Theta.DualPair.Unitary.LeraySplitting` and the standard Weil operator
`r(g ⊗ 1) = standardOperator … (UnitaryGroup.toTraceIsometry g)` of
`Langlands.Theta.Metaplectic.StandardOperator` (GKT Definition 2.9, p. 54).

The module `Langlands.Theta.DualPair.Unitary.LeraySplittingFactor` defines the function `β` of
(11.3) on the whole group as the scalar relating the two operators, proves Theorem 11.6 in its
cocycle form, and computes `β` on every Bruhat cell `P w_S P`.

## Setting

As in `Langlands.Theta.DualPair.Unitary.StandardOperator`: `E / F` quadratic (`hE`), `Q` Hermitian
and invertible (`hQ`, `hQu`), `χ` continuous with `χ|_{Fˣ} = η_{E/F}^{|α|}` (`hres`, GKT (11.2)),
the instances of the module topology, Borel σ-algebra and perfect pairing on `M_{α×ν}(E)`. The
Weil index is `γ = weilIndex (v ↦ (ψ.scale 2⁻¹)(hermitianTraceForm c Q v v))`, the book's
`γ(ψ_{1/2} ∘ Res_{E/F} V)` (`lerayScalar_eq`).

## Content

- `exists_lerayWeil_eq_smul_standardOperator`: there is `z ∈ ℂ¹` with `lerayWeil g = z • r(g ⊗ 1)`:
  `(g ⊗ 1, lerayWeil g)` (`leraySplitting`) and `standardPair (g ⊗ 1)` lie over the same element of
  the symplectic group, so they differ by a scalar (`MetaplecticGroup.exists_scalar_mul_eq`, Schur's
  lemma for the irreducible Schrödinger model); it has absolute value `1` because both operators are
  unitary (`leraySplitting_mem_unitary`, `standardOperator_inner`).
- **`leraySplittingFactor c ν ψ χ Q hc hQ : U(ν, ν) → Circle`**, the function `β` of (11.3), chosen
  as that scalar; `lerayWeil_eq_leraySplittingFactor_smul`: **`lerayWeil g = β(g) • r(g ⊗ 1)` for
  every `g`**; `unitaryStandardPair ψ hc hQ g = (g ⊗ 1, r(g ⊗ 1))` (`standardPair`, GKT
  Definition 2.9) and `leraySplitting_eq_scalar_mul_standardPair`: **the Leray splitting is
  `g ↦ (g ⊗ 1, β(g) r(g ⊗ 1))`** (Corollary 11.7); `standardOperator_toTraceIsometry_ne_zero` and
  `leraySplittingFactor_eq_of_lerayWeil_eq`: `β(g)` is the only such scalar.
- **Theorem 11.6 in cocycle form**: `standardOperator_comp_eq_leraySplittingFactor`,
  `r(g₁ ⊗ 1) r(g₂ ⊗ 1) = β(g₁ g₂) β(g₁)⁻¹ β(g₂)⁻¹ r(g₁ g₂ ⊗ 1)`, and
  `eq_leraySplittingFactor_of_standardOperator_comp`: any scalar `z` of the composition rule
  (`exists_standardOperator_comp`) at `(g₁ ⊗ 1, g₂ ⊗ 1)` is `β(g₁ g₂) β(g₁)⁻¹ β(g₂)⁻¹`. Formal from
  `lerayWeil` being a homomorphism.
- `leraySplittingFactor_mul_mul_of_mem`: `β(p₁ g p₂) = β(p₁) β(g) β(p₂)` (from Proposition 2.17,
  `standardOperator_mul_mul_of_mem`); `leraySplittingFactor_of_mem_siegelParabolic`:
  `β(p) = χ(x(p))⁻¹`; `leraySplittingFactor_weylElement`: `β(w) = γ^{|ν|}` (Proposition 12.29,
  through
  `lerayWeil_eq_inv_smul_standardOperator_of_mem_siegelParabolic` and
  `lerayWeil_weylElement_eq_smul_standardOperator`).
- Blocks, for `σ : ν₁ ⊕ ν₂ ≃ ν`: `blockColsEquiv F E α σ : M_{α×ν₁}(E) × M_{α×ν₂}(E) ≃
  M_{α×ν}(E)` (`blockColsEquiv_apply`, `fromCols_blockColsEquiv`,
  `blockColsEquiv_mul_transpose_map`); `hermitianTracePairing_blockColsEquiv`: the pairing becomes
  `sumPairing`; `toTraceIsometry_blockEmbedding`: the image of `blockEmbedding c σ (g₁, g₂)` is
  `blockDiag (g₁ ⊗ 1, g₂ ⊗ 1)` carried by `isometryGroupCongr`;
  `siegelParabolicRaoValue_blockEmbedding`:
  `x(j(p₁, p₂)) = x(p₁) x(p₂)`; `standardOperator_comp_blockEmbedding`: the composition scalars at
  `(j(g, 1), j(g', 1))` are those at `(g, g')` (Corollary 2.29, `standardOperator_blockDiag_comp`,
  carried by `standardOperator_comp_isometryGroupCongr`).
- `UnitaryGroup.eq_one_of_siegelParabolic_le_ker`: a homomorphism of `U(ν, ν)` trivial on the Siegel
  parabolic is trivial (the relation `w n(1) w = p₀ w n(-1)` of the big cell gives `f(w)² = f(w)`;
  `P` and `w` generate).
- `leraySplittingFactor_blockEmbedding`: **`β_ν(j(h, 1)) = β_{ν₁}(h)`**; the quotient is a character
  of `U(ν₁, ν₁)` (the composition scalars agree and `β` is the coboundary on both sides), trivial on
  the
  Siegel parabolic, hence trivial.
- `normSubgroup_le_ker`, `normQuotientCharacter χ hE hres : Eˣ ⧸ 𝒩(Eˣ) →* Circle`
  (`normQuotientCharacter_mk`): `χ` on the values of the Rao function; `siegelDet_toIsometryGroup`:
  the `siegelDet` of `Langlands.Theta.Metaplectic.RaoFunction` of the image of `p` is
  `siegelParabolicRaoValue p`.
- **The cells.** `leraySplittingFactor_partialWeylElement`: `β(w_S) = γ^{|S|}` (`w_S` is the Weyl
  element of `U(S, S)` embedded in `U(ν, ν)`); `leraySplittingFactor_mul_partialWeylElement_mul`:
  `β(p₁ w_S p₂) = χ(x(p₁) x(p₂))⁻¹ γ^{|S|}`; `leraySplittingFactor_eq_raoFunction`: if the image of
  `g` in `U(W)` lies in `P w_S P` (the cell of the Weyl element `w_S` of the standard basis
  `eᵢ = (0, εᵢ)`, `eᵢ* = -(εᵢ, 0)`), then `β(g) = χ(x(g))⁻¹ γ^{|S|}` with `x` the Rao
  function (Definition 4.37); `leraySplittingFactor_eq`: for every `g`,
  **`β(g) = χ(x(g))⁻¹ γ^{|ν| - dim (X ∩ g X)}`**; `lerayWeil_eq_raoFunction_smul_standardOperator`:
  **`lerayWeil g = χ(x(g))⁻¹ γ^{|ν| - dim (X ∩ g X)} • r(g ⊗ 1)`**. The statements with the Rao
  function take `[NeZero (2 : E)]`, an instance of `Langlands.Theta.Metaplectic.RaoFunction`.

## The book's normalization

GKT (11.3) reads `β(g) = χ^{book}(x_{book}(g)) γ^{s}` on `P w_s P`. The Library's `lerayWeil` is the
book's Leray splitting for `χ^{book} = χ⁻¹` when the book's `W` is the space of rows with the form
`⟨w, w'⟩ = h(w, w')^τ` (then the book's Rao function is the `x` used here, the determinant of
`p|_X` on rows); `leraySplittingFactor_eq` is (11.3) in this reading. Reading the book's `W` instead
as the twisted space `^τW` of GKT Proposition B.6 (same values, `d · w = w d^τ`) gives
`x_{book} = x^τ` and `χ^{book} = χ`, and the same function `β`.

## Declarations

`finiteDimensional_matrix`, `exists_lerayWeil_eq_smul_standardOperator`, `leraySplittingFactor`,
`lerayWeil_eq_leraySplittingFactor_smul`, `unitaryStandardPair`, `weil_unitaryStandardPair`,
`leraySplitting_eq_scalar_mul_standardPair`, `standardOperator_toTraceIsometry_ne_zero`,
`leraySplittingFactor_eq_of_lerayWeil_eq`, `standardOperator_comp_eq_leraySplittingFactor`,
`eq_leraySplittingFactor_of_standardOperator_comp`, `leraySplittingFactor_mul_mul_of_mem`,
`leraySplittingFactor_of_mem_siegelParabolic`, `leraySplittingFactor_weylElement`, `blockColsEquiv`,
`blockColsEquiv_apply`, `fromCols_blockColsEquiv`, `blockColsEquiv_mul_transpose_map`,
`hermitianTracePairing_blockColsEquiv`, `toTraceIsometry_blockEmbedding`,
`siegelParabolicRaoValue_blockEmbedding`, `UnitaryGroup.eq_one_of_siegelParabolic_le_ker`,
`standardOperator_comp_blockEmbedding`, `leraySplittingFactor_blockEmbedding`,
`normSubgroup_le_ker`,
`normQuotientCharacter`, `normQuotientCharacter_mk`, `leraySplittingFactor_partialWeylElement`,
`leraySplittingFactor_mul_partialWeylElement_mul`, `siegelDet_toIsometryGroup`,
`leraySplittingFactor_eq_raoFunction`, `leraySplittingFactor_eq`,
`lerayWeil_eq_raoFunction_smul_standardOperator`. In the name space `Langlands.Theta`.

## Dependencies

`Langlands.Theta.DualPair.Unitary.StandardOperator` (the values on `P` and at `w`),
`Langlands.Theta.DualPair.Unitary.TypeI`, `Langlands.Group.Unitary.Classical` (the comparison with
the isometry group, block embeddings, `w_S`), `Langlands.Theta.Metaplectic.Transport`,
`Langlands.Theta.Metaplectic.Block` (Corollary 2.29), `Langlands.Theta.Metaplectic.RaoFunction`
(`raoFunction`, `raoFunction_eq`), `Langlands.Group.Classical.Bruhat` (the cells).

## Literature

W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025): §11.2.1 and
(11.2), p. 317; (11.3) and Theorem 11.6, p. 318; Proposition 2.17, p. 59; Corollary 2.29, p. 68;
Proposition 12.29, p. 375; Definition 4.37, p. 126.
