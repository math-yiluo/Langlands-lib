# The fppf Picard sheaf of an abelian scheme is separated

Author: Worker 5067.

Helper module for the proof of
`Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeReductionStatement`
(Task 5600). All declarations are in namespace `Langlands.AbelianScheme`, for an arbitrary
scheme `S : Scheme.{u}` and an abelian scheme `A : AbelianScheme S`. Nothing here is
specific to finite-type bases.

## Declarations

- `relativeProjection_app_isIso A T U`: for every `T : Over S` and every open `U` of
  `T.left`, the component at `U` of the sheaf map
  `(relativeProjection A.X.hom).app T` is an isomorphism. Concretely, it is the map
  `O(U) → O(pr⁻¹ U)` on functions along the projection `pr : T ×_S A → T`. The proof changes the
  goal to `(pullback.fst T.hom A.X.hom).app U` and applies the published
  `smoothProperConnectedGlobalFunctions`. The projection is a base change of `A.X.hom`, so
  instance inference shows that it is smooth, proper and has geometrically connected
  fibres.
- `rigidifiedClassSheafIso A`: an isomorphism of presheaves on `Over S` from the Library
  presheaf of isomorphism classes of line bundles rigidified along the unit section,
  `RigidifiedLineBundle.classPresheaf … A.X.hom (unitSection A) (unitSection_comp A)`, to
  the fppf Picard class presheaf `RelativePicard.classSheafPresheaf A.X.hom`. It is the
  Library map `RigidifiedLineBundle.toPicardSheaf`, which is an isomorphism by the
  published `rigidifiedFppfComparison` (the previous lemma supplies its hypothesis on
  functions), composed with the Library isomorphism `RelativePicard.forgetSheafIso`.
- `classSheafPresheaf_diag_isClosedImmersion A`: the diagonal
  `diag (RelativePicard.classSheafPresheaf A.X.hom)` is a representable closed immersion
  (`AlgebraicSpace.IsClosedImmersion`).
- `classSheaf_isSeparated A h`: if `h` says that `RelativePicard.classSheaf A.X.hom` is
  an algebraic space over `S`, then this algebraic space is separated
  (`AlgebraicSpace.IsSeparated`).
- `classSheaf_isQuasiSeparated A h`: under the same hypothesis, it is quasi-separated
  (`AlgebraicSpace.IsQuasiSeparated`).

## Proofs

The diagonal statement uses the Library criterion
`AlgebraicSpace.isClosedImmersion_diag_of_representsEqualizer`. Given `U : Over S` and two
sections `x, y` of the Picard presheaf over `U`, it asks for a closed immersion `ι : Z ⟶ U`
over `S` that represents the locus where `x` and `y` agree. The proof transports `x` and
`y` to rigidified classes by the inverse of `rigidifiedClassSheafIso A`. The published
`rigidifiedClassesEqualizerClosed` then provides a closed immersion `ι : Z → U.left`
that represents the agreement locus of the two rigidified classes. The Picard-side
agreement after pullback along `g : T ⟶ U` is equivalent to the rigidified-side agreement.
This holds because the components of the inverse isomorphism are injective and natural.
The two descriptions of factorizations, through `Over.mk (ι ≫ U.hom)` in `Over S` and
through `ι` in schemes, are then matched by hand.

Separatedness is the diagonal statement read in the algebraic space
`⟨RelativePicard.classSheaf A.X.hom, h⟩`, whose presheaf is
`RelativePicard.classSheafPresheaf A.X.hom`. Quasi-separatedness follows by
`MorphismProperty.relative_monotone`, because a closed immersion of schemes is
quasi-compact.

## Mathematical content

Rigidification along the unit section identifies the Picard sheaf of `A` with rigidified
line bundles. Equality of two rigidified bundles is a closed condition, so the Picard sheaf
is separated. The proof only assembles published Library results and uses no hypothesis on
the base.
