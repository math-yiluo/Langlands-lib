# The affine Weyl image from existence of actual opposite pairs

This internal reduction works at arbitrary universe `u` on the actual
`ValuationBuildingData` and `ParahoricBuildingData` objects. It combines the
published unconditional theorem `RootReflectionProof.hasRootReflections`
with the actual reflection subgroup in `RootReflectionWeyl`. All imported
definitions and statements, including the exact normalizer-image target, are
unchanged.

The imported `reflectionNormalizer_map_le_affineWeylGroup_of_apartment` removes the
explicit fixed-hyperplane premise from the published containment. Its proof
uses the already proved fixed-hyperplane theorem and the supplied apartment
axioms.

The reverse containment needs only existence of an actual
`RelativeRoot.IsOppositeFactorPair` for each nonidentity point of each actual
relative-root group. The uniqueness, reflection, and nonmultipliable-root
clauses of `HasRankOneFactorization` are unnecessary here. The premise uses
the published predicate `RelativeRoot.HasOppositeFactorPairs` from
`RootFactorizationFromExistence`. For each generator
of `W(Ψ)`, include its affine root in `Ψ′`, express that functional by an
actual nonidentity root point using `reflectionAffineRoots_eq`, and choose an
opposite pair using the explicit existence premise. The published
arbitrary-coroot comparison identifies its actual affine action with that
generator. Subgroup closure proves
`affineWeylGroup_le_reflectionNormalizer_map_of_exists_oppositePairs`, and
antisymmetry gives the image equality for `reflectionNormalizer`.

For parahoric data, the published
`reflectionNormalizer_le_simplyConnectedImage` places the actual
representatives in the supplied `G(F)^♮`. Monotonicity of subgroup image then
proves
`affineWeylGroup_le_simplyConnectedNormalizer_map_of_exists_oppositePairs`.
The noncomputable construction `affineWeylRepresentative` chooses a preimage
of each affine Weyl element in the subgroup
`P.simplyConnectedImage.subgroupOf (normalizerPoints P.i)` using that image
containment. Its codomain records both normalizer membership and membership
in the supplied simply connected image.
`normalizerAffineEquiv_affineWeylRepresentative` is the specification of this
choice: its apartment action is the given affine Weyl element. No multiplicative
compatibility or canonicity of these chosen representatives is asserted.

The imported rank-one-predicate adapter
`affineWeylGroup_le_simplyConnectedNormalizer_map_of_apartment`
provides the lower containment, and
`affineWeylGroup_le_simplyConnectedNormalizer_map_of_rankOneStatement`
specializes the existing arbitrary-field statement using the connected
reductivity and maximal splitness already included in `P`.

The final equivalence for a fixed `P`, under the same explicit existence
premise, identifies the remaining obligation for the full image equality.
It is precisely

`P.simplyConnectedImage.subgroupOf (normalizerPoints P.i) ≤
 P.reflectionNormalizer ⊔ P.apartment.normalizerAffineEquiv.ker`.

Replace `W(Ψ)` by the proved image of the reflection subgroup. The reverse
image containment follows from the inclusion of the reflection subgroup in
`G(F)^♮`; the forward containment is equivalent to the displayed algebraic
containment by Mathlib's `Subgroup.map_le_map_iff`.

The provenance is derived from the imported Library proofs and subgroup
calculus. This module proves neither unconditional opposite-pair existence
nor the upper containment for the entire simply connected normalizer. In
particular, it does not prove
`SimplyConnectedNormalizerAffineWeylStatement` or assume AS 5 for a covering
group implicitly. The remaining premises appear explicitly in the Lean
theorems.
