# Trigonalizability is preserved by extension of the base field

Worker 904 wrote this module. `Langlands.GroupScheme.trigonalizableBaseChange` proves
`Langlands.GroupScheme.TrigonalizableBaseChangeStatement.{u}`, which encodes Milne,
*Algebraic Groups* (2017), Corollary 16.4. See the
[statement and source comparison](BaseChangeStatement.md).

Milne embeds `G` in the group `T_n` of upper triangular matrices and extends scalars. The Lean
proof does not use such an embedding. It goes through the internal coordinate predicate
`LineStable` from [`Trigonalizable.CoordinateLine`](CoordinateLine.md), following the published
proof of `Langlands.GroupScheme.IsUnipotent.baseChange` (`Langlands.GroupScheme.Unipotent.BaseChange`).

## Statement of the main lemma

`Langlands.GroupScheme.IsTrigonalizable.baseChange`: let `k` and `K` be fields in universe `u`
with `[Algebra k K]`. Let `H` be a group scheme over `Spec k` with `[IsAffineHom H.X.hom]` and
`IsTrigonalizable H`. Then `IsTrigonalizable` holds for
`(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj H`. No finite-type
hypothesis is needed.

## Helpers (namespace `Langlands.GroupScheme.Trigonalizable`)

For an algebra cogroup `C` in `(CommAlgCat k)ᵒᵖ` over a field `k`:

* `lineStable_of_isTrigonalizable_cogroup`: if the spectrum `(algSpec _).mapGrp.obj C` is
  trigonalizable, then `LineStable k C.X.unop`.
* `isTrigonalizable_cogroup_of_lineStable`: the converse.

Both transport `IsTrigonalizable` along the Library's `Corepresented.cogroupRecoveryIso C` with
`IsTrigonalizable.of_iso`. They then apply the two directions `lineStable_of_isTrigonalizable`
and `isTrigonalizable_of_lineStable` to `Corepresented.cogroupCorepresentation C`. The Library's
`Unipotent.bialgebra_cogroupCorepresentation` identifies its coordinate bialgebra with the
bialgebra structure of `C.X.unop`.

## Proof of `IsTrigonalizable.baseChange`

`H.X.left` is affine. Let `C = AffineCoordinates.coordinateCogroup H` be its coordinate cogroup.
`IsTrigonalizable` moves to `Spec C` along `AffineCoordinates.coordinateCogroupIso H`, so
`LineStable k C.X.unop` holds. `LineStable.baseChange` gives `LineStable K (K ⊗[k] C.X.unop)`.
The scalar-extended Hopf algebra `HopfCoordinates.scalarExtension k K C.X.unop` corresponds to a
cogroup `C'` under `commHopfAlgCatEquivCogrpCommAlgCat`, so
`isTrigonalizable_cogroup_of_lineStable` shows that `Spec C'` is trigonalizable. Finally,
`Spec C'` is identified with the base change of `H`. First, `AffineCoordinates.hopfSpecIso H`
identifies `H` with the spectrum of its Hopf algebra, and this isomorphism is carried through
`GroupScheme.baseChange`. Then the Library's `HopfCoordinates.baseChangeSpecIso` identifies the
base change of that spectrum with the spectrum of the scalar-extended Hopf algebra.
Trigonalizability transfers along the composite by `IsTrigonalizable.of_iso`.

## The target theorem

`trigonalizableBaseChange` introduces the fields, the group scheme `G` and its instances, and
applies `IsTrigonalizable.baseChange`. The hypothesis `[LocallyOfFiniteType G.X.hom]` of the
statement is not used.
