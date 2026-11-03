# Universal coaction on actual pointed affine coordinates

`isInternal_of_iso_splitTorus` proves the coordinate and augmentation
decompositions for a supplied split-torus isomorphism. The exact target theorem
`pointedCoordinateDecomposition` is shared with the character-action construction
in [PointedCoordinateDecompositionProof](PointedCoordinateDecompositionProof.md).
For every universe `u`, field `k`, split torus `S`, affine `V` over `k` and actual
`a : PointedAction S V`, it gives `DirectSum.IsInternal (weightSpace a)` and
`DirectSum.IsInternal (augmentationWeightSpace a)`. Both use the existing weight
spaces, i.e. the eigencondition `f(s.v) = χ(s) f(v)` over every commutative
`k`-algebra, and the existing character lattice `characterLattice S`. Nothing is
assumed about `V` beyond the affine hypothesis already in the target: no group
law, reducedness, finite type, or characteristic hypothesis.

The proof builds the decomposition from the coaction, i.e. from the actual action
at the universal torus point. It follows the module
`Langlands.GroupScheme.Torus.WeightDecomposition`, which does the same for the Lie
algebra. It is the standard comodule argument for a split torus: a coordinate
decomposes into its monomial coaction coefficients. The Lean route is described
below.

## Linear algebra

* `isInternal_comap_of_finsupp`: take a linear map `p : M → (J →₀ M)` that satisfies
  the hypotheses of `Langlands.LinearAlgebra.isInternal_of_finsupp`: coefficients
  lie in `W i`, `p` is `single i` on `W i`, and the coefficients sum back to the
  vector. If a submodule `N` contains every coefficient of each of its elements,
  then the spaces `(W i).comap N.subtype` form an internal direct sum of `N`. The
  proof restricts `p` to `N →ₗ (J →₀ N)` and applies `isInternal_of_finsupp` again.

## General pointed actions

* `pointCoordinates_act_affineMap`: for `φ : A →ₐ[k] B`, an `A`-point `s` of `S`
  and a `B`-point `w` of `V`, the coordinates of `a.act (φ_* s) w` are
  `lift φ (pointCoordinates w) ∘ actionCoordinates a s`. The proof uses the
  naturality of the action (`PointedAction.naturality`) along the algebra map
  `A ⊗[k] Coord V → B` determined by `φ` and `w`.
* `PointedAction.ofIso`: given an isomorphism `e : S.toGrp ≅ S'.toGrp`, this is
  the action of `S'` given by `s' · v = (e⁻¹ s') · v`. Here
  `hom := lift (fst ≫ e.inv) snd ≫ a.hom`, and the origin is unchanged. Its axioms
  follow from those of `a` because `e.inv` is a monoid morphism (`MonObj.one_comp`,
  `MonObj.mul_comp`). `ofIso_act` records the formula for `act`.
* `weightSpace_ofIso`: `weightSpace (a.ofIso e) ψ = weightSpace a (comapIso e ψ)`.
  Here `characterLattice.comapIso e` is the existing pullback of characters, and
  the proof uses `Lie.characterValue_comp` together with `e.hom ≫ e.inv = 𝟙` and
  `e.inv ≫ e.hom = 𝟙`.

## The standard split torus `𝕋 = 𝔾_m^I` (`I` a fintype)

* `monomialCoefficients : k[ℤ^I] ⊗[k] Coord V ≃ₗ[k] ((I → ℤ) →₀ Coord V)` reads off
  monomial coefficients. It is `rTensor` of `AddMonoidAlgebra.coeffLinearEquiv`
  followed by `TensorProduct.finsuppScalarLeft`. Its inverse sends `f` to
  `∑ₘ Xᵐ ⊗ f m` (`monomialCoefficients_symm_apply`,
  `monomialCoefficients_single_tmul`).
* `universalCoaction a := actionCoordinates a (splitTorus.universalPoint I)`. This is
  the actual coaction `Coord V → k[ℤ^I] ⊗ Coord V`, i.e. the action at the
  universal torus point. `coactionCoefficients a` is this map followed by
  `monomialCoefficients`. It is `k`-linear with finitely supported values, and
  `universalCoaction_eq_sum` expands `universalCoaction a z` as
  `∑ₘ Xᵐ ⊗ (coactionCoefficients a z m)`.
* `pointCoordinates_act_universal`: for `φ : k[ℤ^I] →ₐ[k] B` and a `B`-point `w`,
  the `z`-coordinate of `a.act (φ_* U) w` is `∑ₘ φ(Xᵐ) · w(coactionCoefficients a z m)`.
  This combines the two previous items. `coeff_pointCoordinates_act_universal`
  covers the case `B = A[ℤ^I]` with `φ(Xᵐ) = c(m) Xᵐ` and `w` extended from an
  `A`-point. There the coefficient of `Xⁿ` is `c(n) · w(coactionCoefficients a z n)`.
* `coactionCoefficients_mem`: each coefficient `coactionCoefficients a z m` satisfies
  the eigencondition for the character `(splitTorus.characterLatticeEquiv k I).symm m`
  on every commutative `k`-algebra `A`, every `A`-point `s` of `𝕋` and every
  `A`-point `v` of `V`. Let `t` be the units of `s`. The translated evaluation
  `Xᵐ ↦ tᵐ Xᵐ` sends the universal point `U` to `s · U`
  (`splitTorus.universalPoint_translatedEvaluation`, and commutativity of `𝕋`).
  Hence by `act_mul_left` and naturality,
  `a.act (τ_* U) v = a.act (const_* U) (a.act s v)`. Comparing the coefficients of
  `Xᵐ` on both sides with `coeff_pointCoordinates_act_universal` gives
  `pointCoordinates (a.act s v) (coeff_m z) = tᵐ · pointCoordinates v (coeff_m z)`.
  This is the eigencondition, by
  `splitTorus.characterValue_characterLatticeEquiv_symm`.
* `coactionCoefficients_of_mem`: if `z` lies in the weight space for the character
  of `m`, apply its eigencondition to the algebra `k[ℤ^I] ⊗ Coord V`, the point
  `includeLeft_* U` and the universal point `includeRight` of `V`. This gives
  `universalCoaction a z = Xᵐ ⊗ z`, so `coactionCoefficients a z = single m z`.
* `coactionCoefficients_sum`: specialize `pointCoordinates_act_universal` along the
  evaluation `Xᵐ ↦ 1` (`splitTorus.evaluateUnits` at the unit family `1`), which
  sends `U` to the identity point, at the universal point of `V`. Then
  `act_one_left` gives `∑ₘ coactionCoefficients a z m = z`.
* `coactionCoefficients_mem_augmentation`: apply
  `coeff_pointCoordinates_act_universal` at the fixed rational origin, using
  `act_origin` and `pointCoordinates_origin`. This gives
  `origin(coeff_m z) = origin(z)`, so each coefficient of an element of the
  augmentation lies in the augmentation.

## Assembly

* `isInternal_of_iso_splitTorus`: let `a : PointedAction S V` and
  `e : S.toGrp ≅ 𝕋.toGrp`, and put `b := a.ofIso e`. The bijection
  `c : (I → ℤ) ≃+ characterLattice S` is the composite of
  `(splitTorus.characterLatticeEquiv k I).symm` and `characterLattice.comapIso e`.
  Then `p := Finsupp.lmapDomain c ∘ coactionCoefficients b` satisfies the three
  hypotheses of `isInternal_of_finsupp` for `weightSpace a`, transported through
  `weightSpace_ofIso`. This gives the first conjunct. The augmentations of `a` and
  `b` coincide (same origin), so `coactionCoefficients_mem_augmentation` provides
  the stability hypothesis of `isInternal_comap_of_finsupp`. This gives
  `DirectSum.IsInternal (augmentationWeightSpace a)`.
The shared theorem `pointedCoordinateDecomposition` packages the same conclusions
for `IsSplitTorus`; this module retains the universal-coaction construction and
its complete `isInternal_of_iso_splitTorus` assembly.

Both conclusions use the `open Classical` decidable-equality instance on the
character lattice, the same instance as the target statement.
