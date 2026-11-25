# The local restriction formula from the local transfer square

Lean module: `Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionReduction`
(namespace `Langlands.ClassFieldTheory.Global.RelativeWeilGroup`).

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
  `Langlands.ClassFieldTheory.Global.RelativeWeilLocalCosets`).
- **Condition 2 (restriction formula).** This is
  `continuousRestrict_continuousInduceAlong_restrictionInclusion` (module
  `Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionSum`).
- **Condition 1 (transfer).** For `u`, a candidate `eu` with
  `GeometricWeilReciprocityRelation` and `y`, the proof applies
  `transfer_localPlaceMap_of_local` (module `Langlands.ClassFieldTheory.Global.RelativeWeilLocalTransfer`)
  with `a = reciprocityUnits eu y`, condition 3 of `hι`, and two inputs:
  - the idele identity `hG`, which is
    `Langlands.Global.AdelicFunctoriality.prod_ofAdicCompletion_eq_ideleClassInclusion`
    (module `Langlands.ClassFieldTheory.Global.IdeleClassPlaceProduct`) at the place `u`;
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

The final proof of the target, `localInducedRestriction` (module
`Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionProof`), applies this
theorem to the Library proof `Langlands.LocalClassField.extensionWeilTransferReciprocity.{u, u}`
of `ExtensionWeilTransferReciprocityStatement` (module
`Langlands.ClassFieldTheory.Local.WeilTransferReciprocityProof`).

The tower step the module calls is the direct application of the published
`extensionWeilTransferReciprocity_tower`.
