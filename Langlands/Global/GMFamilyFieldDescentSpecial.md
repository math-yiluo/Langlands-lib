# Weighted fibre sums of fine roots vanish on the common kernel of the coarse characters

This module derives the fibre-sum condition of `torusData`
([GMFamilyFieldDescentGroupData](GMFamilyFieldDescentGroupData.md)) from
`LeviWeightFibreDeterminantStatement`. The weighted fibre sums are those in the definition of a
special subspace in J. Arthur, *The invariant trace formula. I. Local theory* (1988), §7, printed
p.355, `arthur-1988-invariant-trace-formula-I`. Declarations are in
`Langlands.GMFamily.FieldDescentTori`.

Setting: `l : M ⟶ G` over `k`, a central split torus `a : A ⟶ M`, a split torus `a₁ : A₁ ⟶ M₁`
over `K` with `m : M₁ ⟶ M_K`, and `j : A_K ⟶ A₁` with `j ≫ a₁ ≫ m = a_K`.

- `fibre_sum_eq_zero`: given `LeviWeightFibreDeterminantStatement`, for a nonzero character `β`
  of `A` and `y` in `fineKernel a₁ m` ([GMFamilyFieldDescentGroups](GMFamilyFieldDescentGroups.md)),
  the sum over the roots `α` of `A₁` in `G_K` with `j ≫ α = β_K` of
  `finrank (weightSpace α) · α(y)` vanishes. The statement gives a rational character `χ` of `M`
  whose fine restriction `fineCharacter a₁ m χ` is the weighted fibre sum
  (`characterRestrict_comp` identifies the restrictions); its functional vanishes on
  `fineKernel a₁ m` by definition. The `finsum` is rewritten as a finite sum over roots: the zero
  character and characters with zero weight space contribute nothing.
- `domRestrict_eval_eq_iff`: two characters of `A₁` have the same functional on the image of
  `fieldCocharacterInclusion j` exactly when their pullbacks along `j` agree (bijectivity of
  scalar extension of characters of a split torus and `eval_injective`).
- `torus_special`: the same vanishing for the roots of a split torus `t : T ⟶ G_K` through which
  `A₁ ⟶ G_K` factors by `g : A₁ ⟶ T`, with fibres taken by restriction of functionals to the image
  of `fieldCocharacterInclusion j`. The fibre of a nonzero restriction is the set of roots `δ`
  with `j ≫ g ≫ δ = β₀_K` for a nonzero `β₀`; regrouping by `α = g ≫ δ` and
  `finrank_weightSpace_comp` reduce it to `fibre_sum_eq_zero`.
