# Representability of the Picard class sheaf from noetherian affine tests

Statement module for
`Langlands.AlgebraicGeometry.Picard.NoetherianAffineTestsPicardExtensionStatement`.

## Statement

`NoetherianAffineTestsPicardExtensionStatement.{u}` is the proposition: for every

- commutative ring `R : Type u` that is noetherian (`IsNoetherianRing R`),
- scheme `X : Scheme.{u}` and morphism `f : X ⟶ Spec R` that is proper
  (`IsProper f`), flat (`Flat f`) and geometrically integral
  (`GeometricallyIntegral f`), and has a section, that is some
  `σ : Spec R ⟶ X` with `σ ≫ f = 𝟙`,
- object `P : Over (Spec R)` whose structure morphism `P.hom` is locally of finite
  presentation,

if there is a natural isomorphism between the two functors on the full
subcategory of `Over (Spec R)` consisting of the tests `T` whose underlying scheme
`T.left` is affine and noetherian,

- the ulifted functor of points `T ↦ ULift (T ⟶ P)` (that is,
  `yoneda.obj P ⋙ uliftFunctor.{u + 1}`), and
- the fppf Picard class sheaf `RelativePicard.classSheafPresheaf f`,

both restricted along the inclusion `ObjectProperty.ι` of that full subcategory,
then `Nonempty ((RelativePicard.classSheafPresheaf f).RepresentableBy P)`: `P`
represents the class sheaf on the whole slice `Over (Spec R)`, that is, on all
test schemes over `Spec R` with no affineness or noetherian condition.

The full subcategory is written inline as
`ObjectProperty.ι (fun T : Over (Spec R) => IsAffine T.left ∧ IsNoetherian T.left)`.
No ample line bundle on `X`, no rigidification and no representing object is
assumed beyond `P` and the isomorphism on noetherian affine tests. The
isomorphism on noetherian affine tests is only assumed to exist, and the
conclusion does not state that the representation restricts to it.

## Role

This is the extension step from noetherian affine tests to all tests for the
Picard class sheaf. Together with a proof of
`NoetherianIntegralFibrePicardNoetherianTestsStatement` (Task 5705's interface
statement, accepted in review and not yet in the Library, which produces such a
`P` and such an isomorphism on noetherian affine tests) it
yields `NoetherianIntegralFibrePicardSheafAFSchemeStatement`, which the Library
reduction `ampleNormalFiniteTypeAbelianPicardSheafAFScheme_of_noetherianIntegralFibre`
turns into `AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement`.

The statement is proved in `NoetherianAffineTestsPicardExtensionProof`
(theorem `noetherianAffineTestsPicardExtension`).

## Provenance

Derived. The statement is the standard reduction of representability of a
functor locally of finite presentation over a noetherian base to locally
noetherian, here noetherian affine, test schemes, specialised to the Picard class
sheaf. Its ingredients in the literature are, in The Stacks Project, Chapter 32
Limits of Schemes (`stacks-limits-of-schemes-a04446e5`, `limits.tex` at commit
a04446e5):

- Proposition 32.6.1 (tag 01ZC, `limits.tex` line 1285): a morphism `P ⟶ S`
  locally of finite presentation has `Hom_S(lim T_i, P) = colim Hom_S(T_i, P)` for
  a directed limit of affine schemes over `S`. This gives the functor-of-points
  side of the extension.
- Lemma 32.10.2 (tag 01ZR, `limits.tex` line 2548) and Lemma 32.10.3 (tag 0B8W,
  `limits.tex` line 2608): finitely presented modules, in particular line bundles,
  and their isomorphisms descend to a stage of a directed limit of affine bases.
  Together with the Library isomorphism
  `RigidifiedLineBundle.properFlatIntegralClassIso` between rigidified line-bundle
  classes and the fppf class sheaf for a proper, flat, geometrically integral
  morphism with a section, this gives the Picard side.

The hypotheses (noetherian base, proper, flat, geometrically integral, section,
`P` locally of finite presentation) are exactly those under which these
ingredients apply; every affine test over a noetherian ring is a directed limit
of noetherian affine tests (spectra of finitely generated subalgebras).
