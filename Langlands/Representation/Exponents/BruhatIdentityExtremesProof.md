# Proof that the identity double coset is Bruhat-extreme (Renard VII.3.1)

Author: Worker 128. Module
`Langlands.Representation.Exponents.BruhatIdentityExtremesProof`.

The theorem `Langlands.Aubert.General.RepresentedParabolic.bruhatIdentityExtremes` has exactly
the published type `BruhatIdentityExtremesStatement.{u}` (module
`Langlands.Representation.Exponents.TemperedBruhatRemarksStatements`). No hypothesis is added.
For a connected reductive `G` over a nonarchimedean local field `F`, with the canonical
evaluation topology `RationalPointFamily.pointTopology` on `G(F)`, it proves:

1. for every represented parabolic `p : P ⟶ G` and every double coset `w` of
   `P(F) \ G(F) / P(F)`, the identity double coset `P(F)` is contained in the closure of `w`
   (`Geometric.BruhatLE`);
2. for represented parabolics `P = MN`, `Q` with rational Levi maps `l : M ⟶ P`,
   `lQ : M ⟶ Q`, `lQ ≫ q = l ≫ p` and `P(F) ∩ Q(F) = M(F)`, every double coset of
   `P(F) \ G(F) / Q(F)` is contained in the closure of `P(F) Q(F)`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, VII.3.1 (printed
pp.232–233 / PDF pp.238–239). Renard deduces the first assertion from the Bruhat decomposition
with its closure relations (Borel–Tits), and the second from the fact that `P(F) P̄(F)` is open
and dense (big cell). The Lean proof of the first assertion takes a different route that avoids
the Bruhat decomposition: it uses only the open cell and the contraction by a cocharacter.
The second assertion follows Renard's route.

## Density of the open cell: `dense_range_dynamicOpenCellMap`

For a cocharacter `χ` of `G`, the open cell
`Ω = {a v⁻¹ : a ∈ P(χ)(F), v ∈ U(χ⁻¹)(F)}` (the range of `HarishChandraSchwartz.openCellMap`,
with `χ⁻¹ = Dynamic.inverseCocharacter χ`) is dense in `G(F)`. The proof repeats the
density argument of the published `dense_identityParabolicDoubleCoset_of_opposite`:
`Plancherel.rationalDynamicOpenCellBoundary` writes the complement of `Ω` as the preimage,
under evaluation at the closed point, of a proper Zariski-closed subset of the scheme of `G`;
`G` is smooth and connected, so its scheme is integral
(`Plancherel.RationalCellConull.noetherian_and_integral`), and
`Plancherel.RationalCellConull.interior_evaluation_preimage_eq_empty` shows that this preimage
has empty interior. Its complement `Ω` is therefore dense.

## The case `Q = P`: `bruhatLE_identityParabolicDoubleCoset_self`

Fix a double coset `w = P(F) g P(F)` and write `[x]` for the double coset of `x`.

1. **Dynamic description.** `parabolicDynamic` (the published proof of
   `ParabolicDynamicStatement`: parabolics are exactly the dynamic parabolics, applied to the
   closed subgroup `p` and using only `IsParabolicSubgroup p`) gives a cocharacter `χ` with
   `SubgroupFunctor.range p = Dynamic.parabolic χ`; via `pointImage_eq_range_carrier`,
   `P(F) = P(χ)(F)`.
2. **The open cell meets its translate.** `Ω` is open, because the open-cell map is an open
   embedding (`HarishChandraSchwartz.isOpenEmbedding_openCellMap_rationalPoint`), and dense by
   the previous section. It contains `1 = 1 · 1⁻¹`, so the left translate `gΩ` is an open set
   containing `g`; density gives a point `a v⁻¹ = g a' v'⁻¹` of `Ω ∩ gΩ` with `a, a' ∈ P(F)`
   and `v, v' ∈ U(χ⁻¹)(F)`. Then `u = a⁻¹ g a' = v⁻¹ v'` lies in `U(χ⁻¹)(F)` and in the
   double coset of `g`.
3. **Contraction.** `BruhatTits.DynamicUnipotentContainment.exists_unit_tendsto_pow_zero` gives
   `t ∈ Fˣ` with `tⁿ → 0`. Let `c = χ⁻¹(t)`. By
   `MatrixRepresentation.mem_unipotent_iff_tendsto_conj` (applied to the cocharacter `χ⁻¹`),
   `cⁿ u c⁻ⁿ → 1` as `n → ∞`. The point `c` lies in the Levi points
   `Z(χ⁻¹)(F) = Z(χ)(F)` (`BruhatTits.DynamicUnipotentContainment.cocharPoint_mem_centralizer`,
   `MatrixRepresentation.cocharPoint_eq_gmRationalPoint_comp`,
   `Dynamic.centralizer_inverseCocharacter`), hence in `P(χ)(F) = P(F)`
   (`RationalPoint.levi_le_parabolic`).
4. **Closure.** An element `z` of the identity double coset has the form `h₁ · 1 · h₂` with
   `h₁, h₂ ∈ P(F)` (`DoubleCoset.mem_quotToDoubleCoset_iff`, `DoubleCoset.eq`), so `z ∈ P(F)`.
   The sequence `z cⁿ u c⁻ⁿ` tends to `z` (continuity of multiplication in the topological group
   `G(F)`, `AlgebraicGeometry.PointTopology.rationalPoint_isTopologicalGroup`), and each term
   lies in `[g]`: it equals `(z cⁿ a⁻¹) g (a' c⁻ⁿ)` with both outer factors in `P(F)`. By
   `mem_closure_of_tendsto`, `z` lies in the closure of `[g]`.

The topology instances used in this part (`IsOpenUnits F`, needed for the open-cell embedding)
come from the local-field structure exactly as in the published
`isOpenCellContraction_dynamic`: `BruhatTits.localField_t2Space`, the right uniform structure of
the additive group, and `isUniformAddGroup_of_addCommGroup`.

## The opposite case: `bruhatLE_identityParabolicDoubleCoset_of_opposite`

`IsRationalLeviSubgroup.exists_unipotentRadical` applied to `lQ` gives a represented geometric
unipotent radical `rQ : U ⟶ Q`. With it, the published
`dense_identityParabolicDoubleCoset_of_opposite` (from
`Langlands.Representation.Intertwining.OppositeIdentitySupportProof`) shows that `P(F) Q(F)`,
the identity double coset, is dense in `G(F)`. Its closure is therefore all of `G(F)`
(`Dense.closure_eq`), so it contains every double coset.

## Assembly: `bruhatIdentityExtremes`

The main theorem introduces the data of the statement, installs the same evaluation topology
on `G(F)`, and combines the two results above. The local-field instances
`[T2Space F]`, `[LocallyCompactSpace G(F)]` and `[NonarchimedeanGroup G(F)]` from the statement
are not needed by the proof.
