# Field-extension descent from its group-theoretic inputs

This module derives `FieldExtensionDescentStatement` from three group-theoretic propositions.
The target formalizes J. Arthur, *An introduction to the trace formula* (2005), Lemma 17.5 and
(17.13), printed pp.99–100, `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`.
[GMFamilyFieldDescentStatement](GMFamilyFieldDescentStatement.md)

- `FieldLeviSplitComponentInclusionStatement` factors the base change of the split
  component of `M` through the split component of `M₁`.
  [FieldLeviSplitComponentStatement](../GroupScheme/Rational/FieldLeviSplitComponentStatement.md)
- `LeviWeightFibreDeterminantStatement` identifies multiplicity-weighted sums of fine roots
  over nonzero coarse characters as restrictions of rational characters.
  [LeviWeightFibreDeterminantStatement](../GroupScheme/Lie/LeviWeightFibreDeterminantStatement.md)
- `LeviSplitComponentRootDatumStatement` identifies the real cocharacter image of the split
  component with a root flat in a split torus. The relative-root reflections are integral and
  preserve weight multiplicities.
  [LeviSplitComponentRootDatumStatement](../GroupScheme/Rational/LeviSplitComponentRootDatumStatement.md)

## Auxiliary lemmas

- `inner_rootVectorIn`, `rootVectorIn_injective`, `rootVectorIn_eq_zero_iff`,
  `mem_actualRootVectors`: the Riesz vector of a character of a split torus in Euclidean
  coordinates.
- `res_rv_eval`, `R_eq_actualRootVectors`: for descent data built by `torusData` from `t : T ⟶ G`
  and `g : A₁ ⟶ T`, the fine roots `D.R` of [GMFamilyFieldDescentRealization](GMFamilyFieldDescentRealization.md)
  are `actualRootVectors (g ≫ t) hA₁ D.e₁`, the Riesz vectors of the roots of `A₁`
  (`mem_roots_comp_iff`).
- `restrictedRoot_rootVectorIn`: if `e : V A ≃ₗ[ℝ] b` satisfies `e x = e₁ (fieldCocharacterInclusion j x)`
  and `j ≫ α = β_K`, the orthogonal projection to `b` of the vector of `α` is the vector of `β`.
- `image_restrictedRoot_erase`: the nonzero projections to `b` of the fine roots are exactly the
  vectors of the roots of `A` (`exists_fine_of_mem_roots`, `exists_coarse_of_mem_roots`).
- `isFieldParameterCompatible_of`: if `b` is the image of `V A`, complementary and orthogonal to
  the image of `fineKernel a₁ m`, then `IsFieldParameterCompatible` holds: write
  `u = ι w + z` with `z ∈ fineKernel a₁ m`; the projection to `b` of `e₁ u` is `e w`, the fine
  character vanishes on `z`, and `eval_fineCharacter_inclusion` evaluates it on `ι w`.
- `hasSpecialWeightSums_of`: if every vector orthogonal to the image of `fineKernel a₁ m` lies in
  `b`, then `HasSpecialWeightSums` holds. A nonempty fibre over `β ≠ 0` is the set of roots with
  `j ≫ α = β₀_K` for a nonzero `β₀`, and `fibre_sum_eq_zero`
  ([GMFamilyFieldDescentSpecial](GMFamilyFieldDescentSpecial.md)) gives the vanishing of the inner
  products.

## The main theorems

`hasActualFieldDescent_of_inputs` proves `HasActualFieldDescent` for nested rational Levi
subgroups, given `LeviWeightFibreDeterminantStatement`, `LeviSplitComponentRootDatumStatement` and
a factorization `j` of the split components. `G_K` is connected reductive
(`connectedReductiveFieldExtensionStatement`), so the root-datum statement over `K` gives
`t : T ⟶ G_K` and `g : A₁ ⟶ T`. `characterRestriction` for `M` and `isCompl_fineKernel` make the
image `B` of `V A` and `K' = fineKernel a₁ m` complementary. `torusData` with the fibre-sum
condition `torus_special` gives descent data `D`. The coordinates are `D.e₁`, the coarse space
`D.b`, and `e` the composite of `LinearEquiv.ofInjective` for `fieldCocharacterInclusion j` with
`Submodule.equivMapOfInjective`. The comparisons are the auxiliary lemmas above together with
`FieldDescentData.inner_e₁_B_K`, `mem_b_of_orthogonal`, `starProjection_mem_b`, and the descent
formula is `FieldDescentData.hasFieldDescentFormula`.

`fieldExtensionDescent_of_inputs` derives `FieldExtensionDescentStatement` from the three
propositions, taking `j` from `FieldLeviSplitComponentInclusionStatement`.
