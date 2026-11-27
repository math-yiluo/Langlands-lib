# Determinant characters of weight spaces of a central split torus: proof

The theorem `Langlands.GroupScheme.leviWeightFibreDeterminant` has type
exactly `LeviWeightFibreDeterminantStatement.{u}`
([statement](LeviWeightFibreDeterminantStatement.md)), in every universe `u`
and with no additional hypotheses. It uses only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## The statement

Let `G` be an affine group scheme locally of finite type over a field `k`,
`l : M ⟶ G` a homomorphism from an affine group scheme `M`, and `a : A ⟶ M` a
central homomorphism from a split torus `A`. Fix a field extension `K/k`, and
write `_K` for base change along `f = algebraBaseMap k K`. For every character
`β` of `A` there is a rational character `χ` of `M` over `k` with the
following property. For every split torus `S` over `K`, every `s : S ⟶ M_K`
and every `j : A_K ⟶ S` with `j ≫ s = a_K`, the restriction along `s` of the
base change `χ_K` is

```
∑ᶠ α with j ≫ α = β_K ,  dim_K weightSpace (s ≫ l_K) α • α .
```

## The witness

The witness is `Lie.stableDeterminantCharacter hV`: the determinant of `M`
acting through `l` and the adjoint representation on the weight space
`V = weightSpace (a ≫ l) β` of `Lie(G)(k)`. It is defined in the module
`Langlands.GroupScheme.Lie.StableSubspaceDeterminant`. Its stability
hypothesis `hV` is `isAdjointStable_weightSpace_of_isCentral`, from the module
`Langlands.GroupScheme.Torus.CentralWeightStability`. Since `a` is central,
the adjoint operators of the points of `M`, after every scalar extension,
preserve the extension of `V`.

## The proof

1. **Base change.** Let `V_K = weightSpace ((a ≫ l)_K) β_K ⊆ Lie(G_K)(K)`. The
   Library's `weightSpaceBaseChangeEquiv` (module
   `Langlands.GroupScheme.Torus.WeightSpaceScalarExtension`) identifies
   `K ⊗[k] V` with `V_K` through `Lie.schemeScalarExtension`
   (`weightSpaceBaseChangeEquiv_tmul`). It carries the base change of the
   basis `Module.finBasis k V` to a basis of `V_K` matched with it. The module
   `Langlands.GroupScheme.Lie.StableSubspaceDeterminantBaseChange` then gives
   stability of `V_K` for `l_K` (`Lie.isAdjointStable_baseChange`) and
   `χ_K = Lie.stableDeterminantCharacter` of `V_K`
   (`Lie.baseChange_stableDeterminantCharacter`).
2. **Fibre decomposition.** Since `j ≫ s = a_K`, the map `(a ≫ l)_K` equals
   `j ≫ (s ≫ l_K)`. The base change `A_K` is a split torus
   (`IsSplitTorus.baseChange`), so `weightSpace_comp_eq_iSup` (module
   `Langlands.GroupScheme.Torus.WeightRestriction`) writes `V_K` as the sum
   of the weight spaces `weightSpace (s ≫ l_K) α` over the characters `α` of
   `S` with `j ≫ α = β_K`.
3. **A weight basis.** The helper theorem `exists_weightBasis_of_eq_iSup` of
   this module turns such a sum into a basis of `V_K` consisting of weight
   vectors for `s ≫ l_K`. The sum of the weights of this basis equals the
   `finsum` above. The weight spaces of the split torus `S` form an internal
   direct sum (`isInternal_weightSpace_of_isSplitTorus`), and only finitely
   many are nonzero (`Submodule.finite_ne_bot_of_iSupIndep`). The basis is
   indexed by `Σ α : t, Fin (dim weightSpace (s ≫ l_K) α)`, where `t` is the
   finite set of characters over `β_K` with nonzero weight space. Its vectors
   are those of the collected basis `DirectSum.IsInternal.collectedBasis`,
   built from `Module.finBasis` of the summands. They are linearly
   independent and span `V_K` (`Module.Basis.span`). Summing over each fibre
   `Fin (dim …)` gives the dimension as multiplicity
   (`Fintype.sum_sigma`, `natCast_zsmul`). The finite sum equals the `finsum`
   by `finsum_cond_eq_sum_of_cond_iff`: a character outside `t` with a nonzero
   summand would have a nonzero weight space.
4. **Torus restriction.** Applying `Lie.characterRestrict_stableDeterminantCharacter`
   to this basis, `characterRestrict s χ_K` is the sum of the weights of the
   basis. On a weight basis the operator of every point of `S` is diagonal,
   so its determinant is the product of the character values
   (`Lie.det_stableOperator_weightBasis`). The split torus `S` is affine
   (`IsSplitTorus.isAffineHom`). Reading the result through
   `rationalCharacters.equivCharacterLattice S` gives the statement.

## Scope

The proof uses no smoothness, connectedness or reductivity of `G` or `M`, and
no finiteness, separability or normality of `K/k`. The weight space
`weightSpace (a ≫ l) β` may be zero, and `β` may be the zero character.
