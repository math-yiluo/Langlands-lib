# The point parahoric lies in the norm-one point stabilizer: proof

Worker 31, task `0fda3c3d-207f-4fdc-9858-1d43ec2bb41e`.

`Langlands.BruhatTits.SpecialCompact.parahoricLeCompactStabilizer` proves
exactly `ParahoricLeCompactStabilizer.{u}` (module
`Langlands.BruhatTits.SpecialCompact.ParahoricStatement`) at arbitrary
universe `u`.

For every nonarchimedean local field `F`, every `G` with
`IsAffineHom G.X.hom`, all `P : ParahoricBuildingData G` and every apartment
point `x`, the theorem proves

`P.parahoricAt x ≤ P.apartment.specialCompactSubgroup x`.

In words, `P_x = j(Z(F)^0) ⊔ G(F)^♯_x` lies in `K_x = G(F)^1 ∩ G(F)_x`.

The theorem has no hypothesis beyond the statement's own binders. In
particular it does not assume V 7 (`IsTopologyCompatible`), any apartment axiom,
`StandardCocharacterStatement` or any other unproved proposition. Lean reports
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## The proof

By definition `P.parahoricAt x = P.parahoric {x}`, the join
`P.centralizerZero.map (rationalPoints.map P.centralizer.j) ⊔ P.sharpFixer {x}`.
Also by definition `P.apartment.specialCompactSubgroup x` is
`P.apartment.compactStabilizer (P.apartment.apartmentMap x)`, the infimum
`rationalCommonNormKernel G ⊓ P.apartment.reducedFixer (P.apartment.apartmentMap x)`.
Both unfoldings hold by `rfl`. The proof applies `sup_le` and treats the two
factors separately.

1. **The `Z(F)^0` factor.** The published theorem
   `ParahoricBuildingData.map_centralizerZero_le_compactStabilizer`
   (module `Langlands.Geometry.Building.KPParahoricFixerComparison`) proves
   `j(Z(F)^0) ≤ P.compactStabilizer (P.apartmentMap x)` with no hypothesis.
   It combines `ZeroSubgroupDatum.centralizerZero_le_rationalCommonNormKernel`
   (`Z(F)^0 ⊆ Z(F)^1`) with `ValuationBuildingData.map_mem_compactStabilizer`,
   which follows from the bundled axiom V 6 on `Z(F)`.

2. **The `G(F)^♯_x` factor.** The proof applies `le_inf`, so it needs two
   inclusions.

   - *Norm one.* The published theorem
     `KPApartmentData.sharpFixer_le_normKernel_of_split` (module
     `Langlands.BruhatTits.SpecialCompact.LeviCompactAlgebraicInclusion`)
     proves `D.sharpFixer {x} ≤ rationalCommonNormKernel G`. It needs only that
     `S` is a split torus, plus the instances `IsAffineHom G.X.hom` and
     `LocallyOfFiniteType G.X.hom`. The proof applies it to
     `D = P.apartment` and `i = P.i`:
     - the split-torus premise is
       `P.isMaximalSplitTorus.isSplitSubtorus.1 : IsSplitTorus P.S.toGrp`;
     - `LocallyOfFiniteType G.X.hom` comes from the instance
       `Smooth G.X.hom`, taken from the bundled field
       `P.isConnectedReductive.smooth`.

     That theorem is the supremum over relative roots of
     `rootGroupPoints_le_rationalCommonNormKernel_of_split`, which is proved
     algebraically, by the route of the task's suggestion. It chooses a
     generic cocharacter `ν` of `S` (`IsSplitTorus.exists_genericCocharacter`),
     which pairs nonzero with every relative root `a`. It replaces `ν` by `-ν`
     if needed so that `⟨a, ν⟩ > 0`. Then
     `RelativeRoot.subgroup_le_dynamicUnipotent` puts the root group
     `U_a(F) = rootGroupPoints P.i a` in the dynamic unipotent `U_G(ν)(F)`.
     `rationalCharacterEval_eq_one_of_mem_unipotent` (module
     `Langlands.Representation.Plancherel.ParabolicLeviLogarithmBounds`) then
     gives `χ(u) = 1` for every rational character `χ`. Its proof chooses a
     unit `t` with `t^n → 0`. For `u ∈ U_G(ν)(F)`, the conjugates
     `ν(t)^n u ν(t)^{-n}` then tend to `1` in the canonical rational-point
     topology of the affine scheme `G`. `χ` is continuous for that topology
     and constant on these conjugates, because its target is commutative.
     Hence `χ(u) = 1`, so `|χ(u)| = 1`. The rational-point topology is a
     published construction on `G(F)`, not a hypothesis, and V 7 is not used.
     The root fixers `U_{a,x,0}` lie in `U_a(F)`, so the generated group
     `G(F)^♯_x` lies in `G(F)^1`.
   - *Fixes `x`.* The published theorem
     `ValuationBuildingData.sharpFixer_le_fixer` (no hypothesis) gives
     `P.sharpFixer {x} ≤ P.fixer (P.apartmentMap x)`. By definition this is
     `P.apartment.reducedFixer (P.apartment.apartmentMap x)`.

The proof supplies all the inputs and adds no premise. The earlier published
`ParahoricBuildingData.parahoricAt_le_compactStabilizer` needs V 7 only for the
norm-one property of the root filtrations. Item 2 replaces that step with the
algebraic root-group argument.

## Library results used

- `Langlands.Geometry.Building.ParahoricBuildingData.map_centralizerZero_le_compactStabilizer`
- `Langlands.Geometry.Building.KPApartmentData.sharpFixer_le_normKernel_of_split`
  (and through it `rootGroupPoints_le_rationalCommonNormKernel_of_split`,
  `IsSplitTorus.exists_genericCocharacter`,
  `RelativeRoot.subgroup_le_dynamicUnipotent`,
  `Langlands.Plancherel.rationalCharacterEval_eq_one_of_mem_unipotent`)
- `Langlands.Geometry.Building.ValuationBuildingData.sharpFixer_le_fixer`
- the fields `ValuationBuildingData.isMaximalSplitTorus`
  (`IsMaximalSplitTorus.isSplitSubtorus`) and
  `ValuationBuildingData.isConnectedReductive` (`IsConnectedReductive.smooth`)

## Scope

This result is the inclusion alone. It does not assert that
`ParahoricBuildingData G` is inhabited, nor any equality, strictness, index,
compactness, maximality or special-vertex property of `P_x` or `K_x`. The
statement's Markdown records the definitions and the Kaletha–Prasad sources
(Notation 2.6.15, Definition 2.6.23, Lemma 2.6.27, Corollary 2.6.28,
Definition 7.4.1). The proof follows the four-step plan in that Markdown.
Step 1 of the plan (rational characters are trivial on the actual root groups)
is carried out by the dynamic-unipotent argument above, and steps 2–3 by the
published `Z(F)^0` result in item 1.
