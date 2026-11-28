# Characters, cocharacters and weights of split tori for field descent

Elementary facts about the characters, real cocharacters and Lie weight spaces of split tori,
used to translate the group data of field descent into linear algebra
([GMFamilyFieldDescent](GMFamilyFieldDescent.md)). All declarations are in the namespace
`Langlands.GMFamily.FieldDescentTori`.

- **Lattices.** `latticePairing_isPerfPair`: the integral pairing between characters and
  cocharacters of a split torus is perfect (transported from the standard split torus by
  `latticePairing_isPerfPair_of_split`). Consequently `eval_injective` and `eval_eq_zero_iff`:
  a character is determined by its real functional `eval T χ` on `V T`. `eval_zero`, `eval_add`,
  `eval_sub`, `eval_zsmul` and the additive map `evalHom` record linearity of `eval`.
- **Functoriality.** `eval_cocharacterMapReal`, `eval_comp_cocharacterMapReal`: for `t : S ⟶ T`,
  evaluating `a` on the image of a real cocharacter of `S` is evaluating `t ≫ a`.
- **Base change.** `cocharacterBaseChangeReal` is scalar extension of real cocharacters from `k` to
  `K`; `eval_baseChange` shows evaluation is compatible with scalar extension of characters
  (`latticePairing_baseChange`). For `j : A_K ⟶ A₁`, `eval_fieldCocharacterInclusion` and
  `eval_fieldCocharacterInclusion_of_eq` evaluate characters of `A₁` on the image of
  `fieldCocharacterInclusion j`: if `j ≫ α` is the scalar extension of `β`, the value of `α` on
  the image of `x` is the value of `β` on `x`.
- **Dimensions.** `finrank_biSup`: the dimension of a finite supremum of independent subspaces is
  the sum of their dimensions. `finrank_weightSpace_comp`: for split tori and `f : T' ⟶ T`, the
  weight space of a nonzero character `ψ` of `T'` for the action through `f` has dimension the sum
  of the dimensions of the weight spaces of the roots `χ` of `T` with `f ≫ χ = ψ`; it combines
  `weightSpace_comp_eq_iSup` with the independence of the weight spaces of a split torus
  (`isInternal_weightSpace_of_isSplitTorus`).
