# The maximal torus `T ∩ 𝒟𝒵(S)` of the semisimple anisotropic kernel

Author: Worker 146 (Task 5619).

This module constructs, over the original field `k`, the maximal torus of the
semisimple anisotropic kernel used in
[`TitsIndexAnisotropicKernelIndexProof`](TitsIndexAnisotropicKernelIndexProof.md).
Its provenance is internal. It composes published Library results, which are
named below. No unproved statement is assumed. All declarations are in
`Langlands.GroupScheme`.

## Maximality of the full intersection

`range_subgroupIntersectionFst_le_torusCentralizer_of_commTarget` works over any
base scheme. Let `d : D ⟶ H` be a monomorphism, `i : T ⟶ H` a commutative
subgroup, and `j : A ⟶ D` and `f : A ⟶ T` maps with `j ≫ d = f ≫ i`. Then the
range of the first projection `D ×_H T ⟶ D` centralizes `j` on every test
scheme. Points of the pullback map into the commutative group `T`, so they
commute with the image of `A` after composition with the monomorphism `d`. This
is the special case `π = 𝟙` of the Library lemma
`range_subgroupIntersectionFst_le_torusCentralizer_of_reflection`
([`Torus/SelfCentralizingPullback`](../Torus/SelfCentralizingPullback.md)),
proved directly by the same argument.

`isMaximalTorus_commutativeSubgroupIntersectionSnd_derived`: let `M` be a
connected reductive group over a field `k`, `i : D ⟶ M` an actual derived
subgroup (`IsDerivedSubgroup i`, with `Mono i.hom.hom` as instance), and
`t : T ⟶ M` a maximal torus. Then the second projection of the full
scheme-theoretic intersection,
`commutativeSubgroupIntersectionSnd t i : (T ×_M D) ⟶ D`, is a maximal torus of
`D`. The Library theorem `derivedMaximalTorusIntersection`
([`Derived/MaximalTorusIntersectionProof`](../Derived/MaximalTorusIntersectionProof.md))
proves only that this intersection is a torus. This module follows its
argument and keeps track of maximality.

1. Pass to `K = AlgebraicClosure k`. By `connectedReductiveFieldExtensionStatement`,
   `M_K` is connected reductive. By `IsDerivedSubgroup.baseChange_of_eq` with
   `derivedSubgroup_baseChange_eq_of_field`, `i_K` is an actual derived subgroup.
   By `maximalTorusBaseChange`, `t_K` is a maximal torus.
2. `IsDerivedSubgroup.exists_compatible_maximalTorus_of_isAlgClosed`
   ([`Rational/GeometricSubgroupTorus`](../Rational/GeometricSubgroupTorus.md))
   gives a maximal torus `j : A ⟶ D_K` and `e : A ⟶ T_K` with
   `e ≫ t_K = j ≫ i_K`. `D_K` is connected reductive
   (`IsDerivedSubgroup.isConnectedReductive`). The Library assembly
   `algClosedMaximalTorusCentralizer_fromQuotient`, with the proved inputs
   `dynamicCentralizerReductive` and `solvableTorusQuotient`, shows that `j` is
   its own centralizer on all test schemes.
3. The lemma above and `selfCentralizingSubgroupIntersectionIso` identify the
   full pullback `D_K ×_{M_K} T_K` with `A`, compatibly with the maps to `D_K`.
   Composing with `pullbackSymmetry` gives an isomorphism from
   `T_K ×_{M_K} D_K` to `A`, whose composite with `j` is the second projection.
   `IsMaximalTorus.iso_comp` therefore makes this second projection a maximal
   torus of `D_K`.
4. `isMaximalTorus_commutativeSubgroupIntersectionSnd_of_baseChange`
   ([`CommutativeSubgroupIntersectionBaseChange`](../CommutativeSubgroupIntersectionBaseChange.md))
   descends maximality to `k`. Its closedness input is `ht.2.1`.

## The setup attached to Tits index data

In the namespace `TitsIndexData`, fix a `k`-group `G` with affine,
locally-finite-type structure morphism, `d : TitsIndexData G`, and
`j : M ⟶ G` with `(torusCentralizer d.splitInclusion).IsRepresentedBy j`.

- `centralizer_isConnectedReductive`: `M` is connected reductive, by the
  published `splitTorusCentralizerReductive` applied to the split torus
  `d.maximalSplit.1.1`.
- `centralizer_isClosedSubgroup`: `j` is a closed subgroup, by
  `IsSplitTorus.isClosedSubgroup_torusCentralizer`.
- `range_inclusion_le_torusCentralizer`: the maximal torus
  `d.pinning.inclusion` of `d` centralizes the maximal split torus. It contains
  that torus through `d.torusMap` (`d.square`), so this is
  `range_le_torusCentralizer_of_factor`.
- `centralizerTorus : d.pinning.torus ⟶ M` is the factorization of
  `d.pinning.inclusion` through `j` (`IsRepresentedBy.liftOfLE`).
  `centralizerTorus_comp` records `centralizerTorus ≫ j = d.pinning.inclusion`.
- `isMaximalTorus_centralizerTorus`: it is a maximal torus of `M`, by
  `IsMaximalTorus.of_comp` and closedness of `j`.
- `kernel_isSemisimple`: for every `i : D ⟶ M` with `IsDerivedSubgroup i`, `D`
  is semisimple, by the published `derivedSubgroupSemisimple`.

Assume also `Mono i.hom.hom`.

- `kernelTorus` is `commutativeSubgroupIntersection (centralizerTorus) i`, the
  full intersection `T ∩ D` inside `M`, as a commutative group scheme.
  `kernelInclusion : kernelTorus ⟶ D` is its second projection.
  `kernelTorusMap : kernelTorus ⟶ d.pinning.torus` is its first projection, as
  a map of commutative group schemes (`groupHom_kernelTorusMap`).
- `kernelInclusion_comp` is the square `T ∩ D ⟶ D ⟶ M` = `T ∩ D ⟶ T ⟶ M`.
  `kernelTorusMap_comp_inclusion` is the square
  `groupHom kernelTorusMap ≫ d.pinning.inclusion = kernelInclusion ≫ i ≫ j`.
  This is the first conjunct of `TitsIndexData.KernelComparison`.
- `isMaximalTorus_kernelInclusion`: `T ∩ D` is a maximal torus of `D`, by the
  theorem of the previous section.
- `isClosedSubgroup_kernelTorusMap`: the first projection is a closed subgroup,
  by `isClosedSubgroup_commutativeSubgroupIntersectionFst` and closedness of
  `i`.
