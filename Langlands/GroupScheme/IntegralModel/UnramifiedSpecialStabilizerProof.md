# The special-stabilizer identity after maximal unramified base change: proof

Module `Langlands.GroupScheme.IntegralModel.UnramifiedSpecialStabilizerProof`.

The main theorem is `Langlands.GroupScheme.IntegralModel.unramifiedSpecialStabilizer`, whose
type is `UnramifiedSpecialStabilizerStatement.{u}`. Let `F` be a non-archimedean local field,
`G` a connected reductive `F`-group, and `M` a model of `G` over `𝒪_F` with connected reductive
special fibre. Write `L = inertiaFixedField F` for the maximal unramified extension. For every
`C : MaximalUnramified.BuildingData F G_L`, there is a special point `x` of the reduced
building of `C` with `M.baseChangeUnramified.integralPoints = C.oneStabilizer x`, and `x` is
the only point fixed by these integral points. This is Bruhat–Tits II, Propositions 4.6.31,
4.6.28(i) and 4.6.29(i).

## Declarations

* `unramifiedSpecialStabilizer_of_pinning M hP C` (reduction). The hypothesis `hP` provides
  a maximal split torus `i : 𝔾_m^I → G_L` that is also a maximal torus and a monomorphism, and
  a split integral pinning `P` for the valuation `MaximalUnramified.valuation F` with
  `P.K = M.baseChangeUnramified.integralPoints`. It also provides a generic cocharacter `ν` of
  `i` with `G(L) = P.K · P_G(ν)(L)`. Under `hP`, the conclusion of the statement holds for
  `C`. Proof: apply `IntegerValuationBuildingData.exists_isSpecialPoint_eq_oneStabilizer_of_pinning`
  (module `SplitIntegralPinningSpecialStabilizer`). Its residue-field hypothesis is
  `MaximalUnramified.infinite_residueField`. Then rewrite with `P.K = integralPoints`.
* `exists_splitIntegralPinning_baseChangeUnramified hG M hSpecial` proves the hypothesis `hP`
  for every good model, as follows.
  1. `R = fixedFieldIntegers F` is Henselian (`fixedFieldIntegersIsHenselian`) and its residue
     field is algebraically closed (`fixedFieldResidueIsAlgClosure`). The model
     `N = M.baseChangeUnramified` is reductive (`isReductive_baseChangeUnramified`). `G_L` is
     connected reductive (`connectedReductiveFieldExtensionStatement`).
  2. `exists_coordinate_fibrewiseMaximalTorus_of_strictHenselian` gives a closed coordinate
     split torus `i : 𝔾_m^I → N.group` that is maximal on every residue-field fibre.
     `localSplitFibrewiseRootDatumExistence` gives a fibrewise root datum `P`, and
     `RootDatumBase.nonempty_base` a base `b`. `localSplitRootGroup` gives root
     parametrizations `u` and the simple Weyl points.
  3. `exists_splitIntegralPinning_genericSplitTorusHom` (module
     `StrictHenselianModelPinning`) gives the monomorphism property and a split integral pinning
     of `N.genericSplitTorusHom i` with subgroup `N.integralPoints`. Its torus condition is
     `baseChangeUnramified_map_genericSplitTorusHom_mem_integralPoints`, and its valuation-ring
     hypothesis is `MaximalUnramified.valuation_le_one_iff_mem_range` (both in module
     `UnramifiedGenericSplitTorus`). Maximality comes from
     `isMaximalSplitTorus_genericSplitTorusHom` and `isMaximalTorus_genericSplitTorusHom`.
  4. The cocharacter is `ν = SplitIntegralPinning.doubleRhoCheck P b` (`2ρ^∨`). It is generic
     by `isGenericCocharacter_doubleRhoCheck`, which uses `isRootDatumOf_genericSplitTorusHom`.
     The Iwasawa decomposition is
     `baseChangeUnramified_exists_integral_mul_parabolic_genericSplitTorus`.
* `unramifiedSpecialStabilizer`: combines the two declarations above. The instance
  `IsAffineHom G.X.hom` is taken from `hG`, as in the statement.

## Supporting modules (part of this proof)

* `Langlands.Geometry.Building.IntegerValuationBuildingBasedTransport`: transport of integer-valued
  building data along a torus isomorphism and a group isomorphism.
* `Langlands.Geometry.Building.SplitIntegralPinningSpecialStabilizer`: the special point of the
  integral subgroup of a split integral pinning on an arbitrary maximal split torus.
* `Langlands.GroupScheme.IntegralModel.StrictHenselianModelPinning`: the split integral pinning
  of the generic fibre of a strictly Henselian reductive model.
* `Langlands.GroupScheme.IntegralModel.UnramifiedGenericSplitTorus` (by Worker 64): torus
  integrality and Iwasawa decomposition along generic split tori of `M.baseChangeUnramified`.
