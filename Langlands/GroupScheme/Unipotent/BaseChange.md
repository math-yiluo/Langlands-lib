# Unipotence is invariant under extension of the base field

Worker 1395 wrote this module. Its main result, `Langlands.GroupScheme.IsUnipotent.baseChange`,
is the forward direction of Milne, *Algebraic Groups* (2017), Corollary 14.9: if `G` is unipotent
over `k` and `k'` is a field extension of `k`, then `G_{k'}` is unipotent. Milne proves it with
coconnected Hopf algebras (14.5). The Lean proof goes through the internal coordinate predicate
`OneMemStable` instead.

## Statement

Let `k` and `K` be fields in universe `u` with `[Algebra k K]`. Let `H` be a group scheme over
`Spec k` such that `H.X.hom` is affine (`[IsAffineHom H.X.hom]`) and `IsUnipotent H` holds. Then
`IsUnipotent` holds for
`(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj H`, the base change
of `H` along `Spec K → Spec k`. `IsUnipotent` is the Library's definition: every nonzero
finite-dimensional matrix representation has a nonzero fixed vector. No finite-type hypothesis is
needed.

## Helpers (namespace `Langlands.GroupScheme.Unipotent`)

* `ofAlgHom_congr`: two bialgebra structures built by `Bialgebra.ofAlgHom` from equal
  comultiplications and counits are equal.
* For an algebra cogroup `C` in `(CommAlgCat R)ᵒᵖ`:
  * `comul_cogroupCorepresentation` and `counit_cogroupCorepresentation`: the coordinate
    comultiplication and counit of the Library's `Corepresented.cogroupCorepresentation C` are the
    cogroup maps `μ` and `η`;
  * `bialgebra_cogroupCorepresentation`: hence its coordinate bialgebra is the bialgebra
    structure of `C.X.unop` itself.
* `oneMemStable_of_isUnipotent_cogroup`: over a field `k`, if the spectrum
  `(algSpec _).mapGrp.obj C` is unipotent, then `OneMemStable k C.X.unop`. The converse is
  `isUnipotent_cogroup_of_oneMemStable`. Both transport `IsUnipotent` along the Library's
  `Corepresented.cogroupRecoveryIso C` and apply the two directions in
  `Unipotent.CoordinateBialgebra`.

## Proof of `IsUnipotent.baseChange`

`H.X.left` is affine. Let `C = AffineCoordinates.coordinateCogroup H` be its coordinate cogroup.
`IsUnipotent` moves to `Spec C` along `AffineCoordinates.coordinateCogroupIso H`, so
`OneMemStable k C.X.unop` holds. `OneMemStable.baseChange` (from `Unipotent.ScalarExtension`)
gives `OneMemStable K (K ⊗[k] C.X.unop)`. The scalar-extended Hopf algebra
`HopfCoordinates.scalarExtension k K C.X.unop` corresponds to a cogroup `C'` under
`commHopfAlgCatEquivCogrpCommAlgCat`, so `isUnipotent_cogroup_of_oneMemStable` shows that
`Spec C'` is unipotent. Finally, `Spec C'` is identified with the base change of `H`. First,
`AffineCoordinates.hopfSpecIso H` identifies `H` with the spectrum of its Hopf algebra and is
carried through `GroupScheme.baseChange`. Then the Library's `HopfCoordinates.baseChangeSpecIso`
identifies the base change of that spectrum with the spectrum of the scalar-extended Hopf
algebra. Unipotence transfers along the composite by `IsUnipotent.of_iso`.
