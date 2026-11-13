# Proof of the reduction of Picard schemeness to the algebraic-space and normal cases

Author: Worker 5067.

`Langlands.AlgebraicGeometry.Picard.finiteTypeAbelianPicardSheafSchemeReduction` proves
`Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeReductionStatement.{u}`:

```lean
FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement.{u} →
  NormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u} →
    FiniteTypeAbelianPicardSheafSchemeStatement.{u}
```

See `FiniteTypeAbelianPicardSheafSchemeReductionStatement.md` for the three propositions.
The proof is a conditional implication. It proves neither premise, so on its own it does
not prove `FiniteTypeAbelianPicardSheafSchemeStatement`.

The theorem is a one-line wrapper around
`finiteTypeAbelianPicardSheafScheme_of_algebraicSpace_of_normal h1 h3`, in the same module
and namespace, which carries the argument. Write `h1` for the algebraic-space premise and
`h3` for the normal-domain AF premise.

## Imported results

From the Library, unchanged:

- `AlgebraicSpace.AFDescentOpenCharts.exists_representation`: if `Y` is an algebraic
  space over `Spec R` that is quasi-separated, and `π : (schemeYoneda _).obj U ⟶ Y.presheaf`
  is finite and surjective with `U.left` AF, then `Y.presheaf` is isomorphic to
  `(schemeYoneda _).obj P` for some `P : Over (Spec R)`. Its first argument is a proof of
  `FiniteSurjectiveQuasiAffineSourceAFStatement`, supplied by the published
  `AlgebraicSpace.finiteSurjectiveQuasiAffineSourceAF`. "AF" means
  `PointTopology.HasFiniteAffineNeighborhoods`: every finite set of points lies in one
  affine open.
- `AlgebraicSpace.LocalRepresentation.chart j H e`: the morphism
  `(schemeYoneda B).obj ((Over.map j).obj H) ⟶ F` induced by a representation `e` of the
  restriction of `F` along `Over.map j`.

From Mathlib: `sigmaOpenCover`, the open cover of a coproduct of schemes by its summands,
and `disjoint_opensRange_sigmaι`, which says the summands have pairwise disjoint images.

From the four helper modules written for this proof (each has its own Markdown file):

- `AbelianScheme.classSheaf_isQuasiSeparated` (`Picard/AbelianPicardSheafSeparated`): if
  the Picard class sheaf of an abelian scheme is an algebraic space, it is quasi-separated.
- `RelativePicard.classSheafPresheafBaseChangeIso f g`
  (`Picard/RelativePicardSheafBaseChange`): the Picard class presheaf of the base change
  `pullback.snd f g` is isomorphic to the restriction `(Over.map g).op ⋙ classSheafPresheaf f`.
- `LocalRepresentation.exists_representation_of_disjoint_cover` and
  `LocalRepresentation.chart_relative` (`AlgebraicSpace/DisjointCoverAFRepresentation`):
  gluing AF local representatives over a finite open cover with disjoint members gives an
  AF representative, and the chart of a representation over `j` inherits every
  base-change-stable property of `j`.
- `MinimalPrimeNormalization.cover R`, `toNormalization`, `ι_cover`, `cover_isFinite`,
  `cover_surjective`, and instances (`NoetherianApproximation/MinimalPrimeNormalizationCover`):
  the finite surjective morphism `∐_p Spec (R ⧸ p)^ν ⟶ Spec R` over the minimal primes `p`,
  and that each `(R ⧸ p)^ν` is an integrally closed domain of finite type over `ℤ`.

## The proof

Fix `R : Type u`, commutative and of finite type over `ℤ`, and an abelian scheme `A` over
`S = Spec R`.

1. **The algebraic space.** `h1 R A` says that the fppf sheaf
   `RelativePicard.classSheaf A.X.hom` is an algebraic space. Call this algebraic space
   `Y`. It is quasi-separated by `classSheaf_isQuasiSeparated`.
2. **The normalization cover.** For each minimal prime `p` let
   `N p = Spec (Normalization R p)`, let `g = cover R : ∐ N ⟶ S`, and let
   `φ p = Spec.map (toNormalization R p) : N p ⟶ S`. Then `φ p = Sigma.ι N p ≫ g` by
   `ι_cover`.
3. **The normal case on each component.** `Normalization R p` is an integrally closed
   domain of finite type over `ℤ` (instances from the helper module, using that `p` is
   prime). So `h3` applied to it and to the base-changed abelian scheme
   `(AbelianScheme.baseChange (φ p)).obj A` gives `H p : Over (N p)` with `(H p).left` AF
   and a representation `r p` of the Picard class presheaf of that base change. The proof
   chooses these by `choose`.
4. **The restricted sheaf.** Let `F' = (Over.map g).op ⋙ classSheafPresheaf A.X.hom`, a
   presheaf on `Over (∐ N)`. It is an fppf sheaf, because it is the underlying presheaf of
   the restriction `(Over.map g).sheafPushforwardContinuous …` of `classSheaf A.X.hom`.
5. **Local representations of `F'`.** For each `p`, an isomorphism
   `e p : (schemeYoneda (N p)).obj (H p) ≅ (Over.map (Sigma.ι N p)).op ⋙ F'` is the
   composite of
   - the Yoneda form of `r p` (`Functor.RepresentableBy.equivUliftYonedaIso`),
   - `classSheafPresheafBaseChangeIso A.X.hom (φ p)`, identifying the Picard presheaf of
     the base change with the restriction along `Over.map (φ p)`, and
   - the isomorphism `Over.map (φ p) ≅ Over.map (Sigma.ι N p) ⋙ Over.map g` from
     `Over.mapCongr` (with `φ p = Sigma.ι N p ≫ g`) and `Over.mapComp`, whiskered by
     `classSheafPresheaf A.X.hom`.
6. **Gluing.** The cover `sigmaOpenCover N` has finite index set (`minimalPrimes R` is
   finite) and its members have pairwise disjoint images (`disjoint_opensRange_sigmaι`,
   converted from opens to sets). `exists_representation_of_disjoint_cover` applied to
   `F'`, this cover, `H` and `e` gives `V' : Over (∐ N)` with `V'.left` AF and an
   isomorphism `E : (schemeYoneda (∐ N)).obj V' ≅ F'`.
7. **The finite surjective chart.** Since `F' = (Over.map g).op ⋙ Y.presheaf`,
   `π = LocalRepresentation.chart g V' E` is a morphism
   `(schemeYoneda S).obj ((Over.map g).obj V') ⟶ Y.presheaf`. It is finite and surjective
   by `chart_relative` with the properties `IsFinite` and `Surjective`, since `g` is
   finite (`cover_isFinite`) and surjective (`cover_surjective`). Its source
   `((Over.map g).obj V').left = V'.left` is AF.
8. **Descent.** `AFDescentOpenCharts.exists_representation finiteSurjectiveQuasiAffineSourceAF`
   applied to `π` and the facts of steps 1 and 7 gives `P : Over S` with
   `(schemeYoneda S).obj P ≅ Y.presheaf = classSheafPresheaf A.X.hom`. Converting back
   with `Functor.RepresentableBy.equivUliftYonedaIso` gives the representation required by
   `FiniteTypeAbelianPicardSheafSchemeStatement`.

## Provenance

Internal. This is the formal proof of the internal reduction statement of Task 5600. The
mathematical route follows Deligne's proof of Faltings–Chai, *Degeneration of Abelian
Varieties*, Chapter I, Theorem 1.9 (printed pp.6–7), up to the normal-base case over the
normalizations of the irreducible components. It then replaces the source's Noetherian
induction and amalgamated sums with descent along the finite surjective normalization
cover. That descent is Gross, *Tensor generators on schemes and stacks*, Theorem 1.2 and
Section 3, in the Library form `AFDescentOpenCharts.exists_representation`. The
statement's Markdown gives the full citations.
