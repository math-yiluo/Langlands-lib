# Ampleness of universal line bundles

Let `S` be a scheme, `F` a `Type v`-valued presheaf on the full slice of
schemes over `S`, and `L : PresheafLineBundle F` coherent actual line-bundle
data. The scheme universe `u` and value universe `v` are arbitrary.

`PresheafLineBundle.IsAmple` is the proposition that there exist a scheme
over `S` and a representation of `F` by that scheme for which the
universal line bundle is ample. Thus this definition includes the
existence of a representer; it does not assign ampleness vacuously to an
unrepresented presheaf.

`universal_isAmple_of` transports ampleness of `L.universal e` from one
supplied representation `e` to any other supplied representation `d` of
the same presheaf. The canonical isomorphism `d.uniqueUpToIso e` in the
slice induces an isomorphism of the underlying schemes, hence an affine
morphism. The proof pulls back the ample bundle along this morphism
using `LineBundle.IsAmple.pullback_of_isAffineHom`. It then uses
`L.universalCompareIso d e` and the forgetful functor from line bundles
to module sheaves to transport ampleness to `L.universal d` by
`LineBundle.IsAmple.of_iso`.

`universal_isAmple_iff` applies this argument in both directions. Thus
ampleness of the universal bundle is independent of the supplied
representing scheme.

`isAmple_iff_universal` identifies `L.IsAmple` with ampleness of
`L.universal e` for any supplied representation `e`. The forward
implication transfers ampleness from the representation in the
existential witness, and the reverse implication uses `e` itself as
that witness.

`reindex_universal_isAmple_iff` also allows a presheaf isomorphism
`φ : G ≅ F` and arbitrary supplied representations of `G` and `F`.
Reindexing `L` along `φ.hom` gives a universal bundle whose ampleness is
equivalent to that of `L` on the supplied representation of `F`.
The proof identifies the reindexed universal bundle with the bundle
evaluated at the transported representation `e.ofIso φ` and applies
`universal_isAmple_iff`.

`reindex_isAmple_iff` deduces that reindexing along `φ.hom` preserves the
intrinsic `IsAmple` property itself. It transports the representing
witness along `φ` or `φ.symm` and uses the preceding comparison to
transport the ampleness proof.

This is internal derived content from the coherent universal-bundle
comparison, affine pullback preservation of ampleness, and transport of
ampleness along an actual module-sheaf isomorphism. The lemmas compare
supplied representations and ampleness hypotheses; they do not
construct initial ampleness or a representer without those inputs.
No condition on the base scheme or smoothness or properness of the
representers is needed for these comparisons.
