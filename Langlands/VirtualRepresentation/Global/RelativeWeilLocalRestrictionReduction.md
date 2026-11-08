# The local restriction formula from the local transfer square

Lean module: `Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionReduction`
(namespace `Langlands.ClassField.Global.RelativeWeilGroup`).

## Statement

`localInducedRestriction_of_extensionSquare` takes one hypothesis,

`hsq : Langlands.LocalClassField.ExtensionWeilTransferReciprocityStatement.{u, u}`,

and proves `LocalInducedRestrictionStatement.{uV, u}`. The hypothesis is the published local
transfer square for one embedding of p-adic fields (Serre, *Local Fields*, XI §3, diagram (2)),
at equal universes. This module does not prove that square. It shows that the published
target follows from the square and nothing else. The universes `uV` and `u` stay free. The
theorem adds no hypothesis on the class family, the fields, the place, the reciprocity
candidates or the representations.

## Proof

Let `c`, `h : Restriction c`, `F ⊆ K ⊆ E` with `E/F` Galois, `z`, `w` above `z`, `e` and
`ι` with `hι : IsLocalRelativeWeilMap z w e ι` be given. Then `E/K` is Galois
(`IsGalois.tower_top_of_isGalois`). Condition 2 of `hι`, read for `discreteLocalMap ι`, is
`hι'`.

- **Local maps.** `ιu := localPlaceMap c K z w h (discreteLocalMap ι) hι' u` (module
  `Langlands.ClassField.Global.RelativeWeilLocalCosets`).
- **Condition 2 (restriction formula).** This is
  `continuousRestrict_continuousInduceAlong_restrictionInclusion` (module
  `Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionSum`).
- **Condition 1 (transfer).** For `u`, a candidate `eu` with
  `GeometricWeilReciprocityRelation` and `y`, the proof applies
  `transfer_localPlaceMap_of_local` (module `Langlands.ClassField.Global.RelativeWeilLocalTransfer`)
  with `a = reciprocityUnits eu y`, condition 3 of `hι`, and two inputs:
  - the idele identity `hG`, which is
    `Langlands.Global.AdelicFunctoriality.prod_ofAdicCompletion_eq_ideleClassInclusion`
    (module `Langlands.ClassField.Global.IdeleClassPlaceProduct`) at the place `u`;
  - the local identity `htower`: the transfer of `upperReciprocity e` at `y` equals
    `twistedMap (reciprocityUnits eu y)`. This is the published
    `Langlands.LocalClassField.extensionWeilTransferReciprocity_tower` (module
    `Langlands.ClassFieldTheory.Local.WeilTransferReciprocityTower`) for the tower
    `F_z → K_u → E_w`, with `fK = completionPadicAlgHom z u`, `fE = completionPadicAlgHom z w`
    and `g = twistedMap` viewed as a `ℚ_p`-algebra map (`AlgHom.restrictScalars`, using the
    published instances `(towerPadicField z _).algebra` and `towerPadicField_isScalarTower`).
    Its compatibility hypothesis is `completionClosureEmbedding_twistedMap`, and it uses `hsq`,
    the relation for `eu`, and condition 1 of `hι` (the relation for `e`). Its subgroup
    `(extensionWeilMap F K fK).range.comap …` and its identification through `rangeInverse`
    are, definitionally, `upperSubgroup` and `upperReciprocity`.

## Use

The final proof of the target applies this theorem to a Library proof of
`ExtensionWeilTransferReciprocityStatement.{u, u}` once that proof is published (task
`2b6541a9-9007-4cc5-9a23-f5785fce6d55`).

## Authors

Worker 1831 wrote the module. The tower step it calls was first written by Worker 1828 in this
module's draft (`towerTransferSquare_of_extension`), and is now the direct application of
their published `extensionWeilTransferReciprocity_tower`.
