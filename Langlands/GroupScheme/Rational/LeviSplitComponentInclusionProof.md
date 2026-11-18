# Inclusion of split components of nested rational Levis

`Langlands.GroupScheme.leviSplitComponentInclusion` proves
[`LeviSplitComponentInclusionStatement`](LeviCentralCompatibilityStatements.md).
Over an arbitrary field, let `M` and `L` be rational Levi factors in a
connected reductive group `G` and let `m : M ⟶ L` satisfy
`m ≫ lL ≫ q = lM ≫ p`. The theorem factors the supplied split component
`aL : AL.toGrp ⟶ L` through the supplied split component `aM : AM.toGrp ⟶ M`.

## Proof

`leviSplitComponentCentralizer` identifies the centralizer of the image
of `AM` in `G` with the subgroup functor represented by
`lM ≫ p`. The ambient map of `AM` factors through `L` by
`aM ≫ m`. Because `aL` is central in `L`,
`IsCentral.range_comp_le_torusCentralizer_of_factor` puts the image of
`aL ≫ lL ≫ q` in that centralizer on every test scheme and after every
change of test scheme.

`SubgroupFunctor.IsRepresentedBy.factorHom` lifts this map to
`g : AL.toGrp ⟶ M`. Canceling the closed embedding `lL ≫ q` gives
`g ≫ m = aL`. The morphism `m` is a closed embedding because its
composite with `lL ≫ q` is the closed embedding `lM ≫ p`.
`IsCentral.of_comp` therefore shows that `g` is central in `M`.
Since `M` is affine and `AL` is a split torus, `IsSplitComponent.exists_factor`
gives a group-scheme factorization of `g` through `aM`. `Additive.ofMul`
views the resulting morphism as `f : AL ⟶ AM`, and the factorization gives
`CommGroupScheme.groupHom f ≫ aM ≫ m = aL`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`. The inclusions
`A_G ⊂ A_M` and `A_L ⊂ A_M` occur in V.3.6 (printed p. 111,
PDF p. 117) and V.3.13 (printed p. 112, PDF p. 118), respectively. The
case `L = G` gives the factorization in V.3.6, and nested standard Levis
give the `A_L ⊂ A_M` inclusion in V.3.13.
