# The star action of a quasi-split group is the natural action: proof

This module proves the published proposition
`Langlands.GroupScheme.StarActionQuasiSplitStatement`
([`StarActionQuasiSplitStatement`](StarActionQuasiSplitStatement.md)) as the theorem
`Langlands.GroupScheme.starActionQuasiSplit`. Source: Milne, *Algebraic Groups* (2022
corrected reprint), source `milne-2022-algebraic-groups`, Proposition 25.28(a), the direction
"quasi-split implies natural action", with §25.c, printed p.555 (PDF 566). Milne's proof
chooses the Borel subgroup over `k`, so that the base is stable under the Galois group. The
implemented route is the classical one: choose the Galois pinning data on a maximal torus
inside a `k`-Borel subgroup, with the base attached to that Borel subgroup; the ordinary
Galois action then preserves the base, so no Weyl correction is needed.

The Lean proof was written by Worker 3483 (shared draft revision 7 of Task 3483) and is
submitted unchanged for Task 5456; the Markdown of the three modules was completed with the
modules of all published inputs.

## Statement proved

For every field `k : Type u` and group scheme `G` over `Spec k` with affine and locally
finite type structure map and `IsQuasiSplit G`, there is
`d : GaloisPinningData k (SeparableClosure k) G` with
`(d.starAction σ).val = d.galoisAction σ` for every `σ ∈ Aut_k(k_s)`.

The theorem `starActionQuasiSplit` has type exactly `StarActionQuasiSplitStatement.{u}`, at
the statement's universe parameter `u`, with no additional hypothesis.

## Route

1. `StarActionQuasiSplit.exists_isMaximalTorus_comp_of_isGeometricBorel` (internal lemma of
   this module). `IsQuasiSplit G` supplies connected reductivity and a geometric Borel
   subgroup `b : B ⟶ G` (its fields `isConnectedReductive` and
   `exists_isGeometricBorelSubgroup`, `Reductive/QuasiSplit`); `B` has affine structure map by
   `BorelFieldExtension.isAffineHom_source` (`Absolute/BorelFieldExtensionFields`), and
   `G_{k̄}` is connected by `IsConnectedReductive.connectedSpace_toAlgebraicClosure`
   (`GeometricConnectedness`). Over `k̄`, the published `borelMaximalTorus`
   (`Absolute/BorelMaximalTorusProof`) gives a maximal torus of `G_{k̄}` through `B_{k̄}`.
   The published `exists_isMaximalTorus_comp_of_geometric`
   (`Absolute/ParabolicIntersectionTorusReduction`), applied to `maximalTorusExistence`
   (`Torus/ExistenceProof`), `maximalTorusBaseChange` (`Torus/MaximalBaseChangeProof`) and
   `maximalTorusConjugacy` (`Absolute/MaximalTorusConjugacyProof`), then gives a torus `T`
   over `k` and `t : T ⟶ B` with `t ≫ b` a maximal torus of `G`.
2. Over `E = k_s`: `T_E` is split (`GaloisPinningData.isSplitTorus_separableClosure`,
   `Reductive/AbsoluteStarAction`); `G_E` is connected reductive
   (`connectedReductiveFieldExtensionStatement`, `Reductive/FieldExtensionProof`);
   `(t ≫ b)_E` is a maximal torus (`maximalTorusBaseChange`); and `rootDatumExistence`
   (`Reductive/RootDatumExistence`) gives a reduced root datum `P` of `(G_E, T_E)`.
3. `b_E` is a Borel subgroup by `StarActionQuasiSplit.isBorelSubgroup_separableClosure`
   ([`StarActionQuasiSplitBorel`](StarActionQuasiSplitBorel.md)). Clause 3 of the published
   `regularCocharacterBorel` (`Absolute/RegularCocharacterBorelProof`) gives a cocharacter
   `ν` of `T_E`, regular for `(t ≫ b)_E`, with `b_E` representing `P(ν ≫ (t ≫ b)_E)`.
4. The base is `IsRootDatumOf.regularCocharacterBase` (`Reductive/RegularCocharacterPinning`)
   for `ν`; regularity for `P` follows from `IsRootDatumOf` (the pairing of `P` is the
   lattice pairing and its roots are the actual roots). The pinning is
   `RootPinning.ofSplitMaximalTorus` (`Reductive/RootPinningFromSplitTorus`) for this base.
   These data, with torus `T` and inclusion `t ≫ b`, form `d`.
5. Positive roots. By `IsRootDatumOf.regularCocharacterBase_isPos`
   (`Reductive/RegularCocharacterPinning`), a root index is positive exactly when its root
   pairs positively with `ν`. By
   `StarActionQuasiSplit.mem_roots_iff_of_isRepresentedBy_parabolic_of_comp`
   ([`StarActionQuasiSplitRoots`](StarActionQuasiSplitRoots.md)), that holds exactly when the
   root is a root of `t_E : T_E ⟶ B_E`. Thus the positive roots of the base are the roots of
   the `k`-defined map `t` into the `k`-subgroup `B`.
6. The published `IsRootDatumOf.galoisRootIndexEquiv_mem_support_iff`
   (`Reductive/RootDatumGaloisSimpleRoots`) then shows that the ordinary Galois root-index
   action preserves the simple roots. By
   `IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus_indexEquiv`
   (`Reductive/RootDatumGaloisCoroots`), this says that `d.galoisAction σ` lies in
   `d.toSplitPinning.basedRootDatumAut`, and the published
   `GaloisPinningData.starAction_eq_galoisAction` (`Reductive/StarAction`) concludes.

## Published inputs

Every published Library theorem used by this module and its two helper modules
`StarActionQuasiSplitRoots` and `StarActionQuasiSplitBorel`, by module (all modules under
`Langlands.GroupScheme`; names in namespace `Langlands.GroupScheme`):

- `Reductive.QuasiSplit`: the fields `IsQuasiSplit.isConnectedReductive`,
  `IsQuasiSplit.exists_isGeometricBorelSubgroup`, and the definition
  `IsGeometricBorelSubgroup` (a Borel subgroup over `k` and over `k̄`).
- `Absolute.Borel` and `Reductive.Basic`: the fields `isClosedSubgroup`, `smooth`,
  `connectedSpace` and `maximal` of `IsBorelSubgroup`, and `smooth`, `isAffineHom` of
  `IsConnectedReductive`.
- `GeometricConnectedness`: `IsConnectedReductive.connectedSpace_toAlgebraicClosure`,
  `connectedSpace_baseChange_of_smooth_affine`.
- `Absolute.BorelFieldExtensionFields`: `BorelFieldExtension.isAffineHom_source`,
  `BorelFieldExtension.isBorelSubgroup_baseChange_of_maximal`.
- `Absolute.BorelMaximalTorusProof`: `borelMaximalTorus`.
- `Absolute.ParabolicIntersectionTorusReduction`: `exists_isMaximalTorus_comp_of_geometric`.
- `Torus.ExistenceProof`: `maximalTorusExistence`.
- `Torus.MaximalBaseChangeProof`: `maximalTorusBaseChange`.
- `Absolute.MaximalTorusConjugacyProof`: `maximalTorusConjugacy`.
- `Reductive.AbsoluteStarAction`: `GaloisPinningData.isSplitTorus_separableClosure`.
- `Reductive.FieldExtensionProof`: `connectedReductiveFieldExtensionStatement`.
- `Reductive.RootDatumExistence`: `rootDatumExistence`.
- `Absolute.RegularCocharacterBorelProof`: `regularCocharacterBorel`.
- `Reductive.RegularCocharacterPinning`: `IsRootDatumOf.regularCocharacterBase` (definition),
  `IsRootDatumOf.regularCocharacterBase_isPos`.
- `Reductive.RootPinningFromSplitTorus`: `RootPinning.ofSplitMaximalTorus` (definition).
- `Reductive.RootDatumGaloisCoroots`:
  `IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus_indexEquiv`.
- `Reductive.RootDatumGaloisSimpleRoots`: `IsRootDatumOf.galoisRootIndexEquiv_mem_support_iff`.
- `Reductive.StarAction`: `GaloisPinningData.starAction_eq_galoisAction`.
- `Absolute.RegularCocharacterMaximal`: `lieKernelMapLinear_targetMapLinear`,
  `adjoint_comp_targetMapLinear`, `targetMapLinear_mem_weightSpace`,
  `exists_lieKernel_of_mem_nonnegativeWeightSpan`.
- `Absolute.RegularCocharacterWeights`: `nonnegativeWeightSpan_def`,
  `iSup_nat_weightSpace_cocharacter_eq_nonnegativeWeightSpan`, `weightSpace_disjoint_iSup`.
- `Dynamic.LieProof`: `dynamicLie`.
- `Lie.KernelTargetMaps`: `Lie.targetMapLinear_injective`.
- `SubgroupFunctor`: `SubgroupFunctor.mem_range`.
- `Descent.Data`: `Descent.pullbackComparison` (definition),
  `Descent.pullbackComparison_naturality`.
- `SubgroupBaseChange`: `IsClosedSubgroup.baseChange`.
- `Rational.SplitRankTransport`: `IsClosedSubgroup.comp_iso`.
- `Absolute.SolvableFieldExtensionProof`: `solvableFieldExtensionStatement`.
- `BaseChangeReflection`: `fieldExtension_fpqc`, `isIso_of_baseChange`.

The remaining lemmas are general Mathlib facts (`Functor.map_comp`, `Set.mem_range_self`,
`Submodule.exists_mem_ne_zero_of_ne_bot`, `Submodule.disjoint_def`, `Submodule.mem_bot`,
`le_iSup₂`, `IsScalarTower.algebraMap_eq`, `Spec.map_comp`).

No hypothesis beyond those of the statement is used; there is no restriction on the
characteristic or perfectness of `k`. The module sets `maxHeartbeats 800000` and
`backward.isDefEq.respectTransparency false`. `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound`.
