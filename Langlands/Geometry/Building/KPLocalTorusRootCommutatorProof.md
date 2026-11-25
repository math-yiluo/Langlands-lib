# Positive-depth torus action on root-group filtrations over `K = F^ur`

Module `Langlands.Geometry.Building.KPLocalTorusRootCommutatorProof`.

```
theorem kpLocalTorusRootCommutator : KPLocalTorusRootCommutatorStatement.{u}
```

The theorem `Langlands.Geometry.Building.kpLocalTorusRootCommutator` proves exactly
`KPLocalTorusRootCommutatorStatement.{u}` (module
`Langlands.Geometry.Building.KPLocalTorusRootCommutatorStatement`), at an arbitrary universe
`u`. It covers every nonarchimedean local field `F` of any characteristic, every affine group
scheme `H` over `K = UnramifiedClosure F`, all building data `B` whose centralizer `Z` is a
torus, every apartment point `x`, every relative root `a` (multipliable and divisible roots
included) and all `r s : ℝ≥0` with `0 < r`. If `t` lies in
`localGeometricCharacterCongruence F (B.centralizerTorus hZ) r` and `u ∈ B.filtration x a s`,
then with `z = j(t)` the commutator `z u z⁻¹ u⁻¹` lies in
`B.apartment.filtrationBlock x (fun _ => r + s) a`, the block `U_{a,x,r+s} · U_{2a,x,r+s}`
of KP Definition 7.3.3(1). This is the `K`-level form of KP Lemma 7.2.3.

## Proof

The proof is a single application:

```
kpLocalTorusRootCommutator_of_valuedRankOneCoordinates quasiSplitValuedRankOneCoordinates
```

It uses two results.

* `kpLocalTorusRootCommutator_of_valuedRankOneCoordinates`, in the module
  `Langlands.Geometry.Building.KPLocalTorusRootCommutatorReduction`. It
  proves `QuasiSplitValuedRankOneCoordinatesStatement.{u} → KPLocalTorusRootCommutatorStatement.{u}`.
  Its paired Markdown describes the argument. In outline:
  * every relative root is an indivisible root `b`, or the double `2b` of one
    (`HasOppositeFactorPairs.eq_one_or_two_of_nsmul_mem`);
  * the point `x` is a translate of the coordinate origin of `b`
    (`KPApartmentData.equipollent_of_mem`);
  * `z = j(t)` acts on the coordinates through a coordinate character `χ` with
    `r ≤ w(χ - 1)`. This bound is `coordinateCharacter_mem_unitFiltration` from the published
    module `KPLocalCoordinateCharacterCongruence`.
  * The commutator is then computed in the three cases:
    * the `SL_2` case, where `2b` is not a root;
    * the `SU_3` case `a = b`, using the published
      `SU3Root.Parameters.scale_mul_inv_mem_filtration_product` from
      `SU3RootScalingCommutator`;
    * the divisible case `a = 2b`, using `SU3Root.Parameters.scale_mul_inv_mem_centralFiltration`.
* `quasiSplitValuedRankOneCoordinates`, the published proof of
  `QuasiSplitValuedRankOneCoordinatesStatement.{u}` (module
  `Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinatesProof`). For each indivisible relative root `b` of `B` it gives valued `SL_2` coordinates
  when `2b` is not a root and valued `SU_3` coordinates when `2b` is a root.

The proof adds no premise and assumes no unproved proposition. The hypothesis `0 < r` of the
target is not used. The statement pair and the modules it imports are unchanged. The axioms
used are `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The module is the final composition step of the proof of
`KPLocalTorusRootCommutatorStatement` and has no separate literature
counterpart. The source of the target is documented in `KPLocalTorusRootCommutatorStatement.md`:
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Lemma 7.2.3 and Definition
7.3.3(1). The case split in the reduction follows the `SL_2` and `SU_3` computations in the
proof of KP Proposition 7.1.1. The `SU_3` group law is KP (2.7.2).

The supporting modules `SU3RootScalingCommutator` and
`KPLocalCoordinateCharacterCongruence` are both used by the reduction. The second
builds on `KPLocalCoordinateValuationComparison`.
