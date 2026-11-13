# The Picard class sheaf is represented once it is represented on noetherian affine tests

Helper module for `noetherianAffineTestsPicardExtension`, the proof of
`Langlands.AlgebraicGeometry.Picard.NoetherianAffineTestsPicardExtensionStatement`
(a step towards
`Langlands.AlgebraicGeometry.Picard.AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement`).
It proves the extension step from noetherian affine tests to all tests for the
fppf Picard class sheaf. It uses the general glueing results of
`NoetherianAffineTestsUniversalElement`.

## Main theorem

`nonempty_representableBy_of_noetherianAffine`: let `R` be a noetherian ring in
universe `u`. Let `f : X ⟶ Spec R` be proper, flat and geometrically integral, with
a section `ε` (`ε ≫ f = 𝟙`). Let `P : Over (Spec R)` with `P.hom` locally of finite
presentation. Suppose `α` is a natural isomorphism, on the full subcategory of
tests `T : Over (Spec R)` whose underlying scheme is affine and noetherian, between
the ulifted functor of points `Hom_{Spec R}(T, P)` and the fppf Picard class sheaf
`RelativePicard.classSheafPresheaf f`. Then
`Nonempty ((RelativePicard.classSheafPresheaf f).RepresentableBy P)`, that is, `P`
represents the class sheaf on the whole slice `Over (Spec R)`.

No hypothesis on `X` beyond those listed is used; in particular no ample line
bundle is needed for this step.

Proof as implemented:

1. `P.left` is locally noetherian, being locally of finite type over a noetherian
   base (`LocallyOfFiniteType.isLocallyNoetherian`).
2. `exists_universal_map` (from `NoetherianAffineTestsUniversalElement`) gives
   `ξ ∈ classSheaf f (P)` with `F.map g.op ξ = α(g)` for every noetherian affine
   test `T` and every `g : T ⟶ P`. So `g ↦ F.map g.op ξ` is bijective on every
   noetherian affine test.
3. `bijective_of_isAffine` (below) extends this bijectivity to every test with
   affine underlying scheme.
4. `representableByOfBijectiveAffine` (from `NoetherianAffineTestsUniversalElement`)
   turns `ξ` into a representation.

## Auxiliary declarations

- `sheafClassOf_eq_of_iso`: isomorphic line bundles on `X ×_S T` have the same
  class in the fppf sheaf (via `classOf_eq_iff_iso` and `toClassSheaf`).
- `bijective_of_iso`: for a presheaf `F` and `ξ ∈ F(P)`, bijectivity of
  `g ↦ F.map g.op ξ` on `Hom(T, P)` transfers along an isomorphism `T ≅ T'`.
- Section `Rigidified`, for `f : X ⟶ S` proper, flat, locally of finite
  presentation and geometrically integral with a section `ε`. All three lemmas use
  the Library isomorphism `RigidifiedLineBundle.properFlatIntegralClassIso f ε hε`
  between rigidified line-bundle classes and the fppf class sheaf on the whole
  slice.
  - `exists_rigidified_sheafClassOf`: every section of the class sheaf over a test
    `T` is the class `sheafClassOf f T` of the underlying line bundle of a
    rigidified line bundle on `X ×_S T`.
  - `nonempty_iso_of_sheafClassOf_eq`: if two rigidified line bundles have the
    same class in the sheaf, their underlying line bundles are isomorphic. The
    comparison map is injective, so the rigidified classes agree, so the
    rigidified bundles are isomorphic; forget the rigidification.
  - `nonempty_pullback_iso_of_map_eq`: if the classes of two rigidified line
    bundles on `X ×_S U` agree after restriction along `h : T ⟶ U`, the pullbacks
    of their underlying line bundles to `X ×_S T` are isomorphic. Uses
    `map_sheafClassOf` and `RigidifiedLineBundle.relativePullback`.
- Section `Stages`, over `Spec R`, with `affineBase R A` the test `Spec A` of an
  `R`-algebra `A`, and `affineSubalgebraMap B : Spec A ⟶ Spec B` and
  `affineAlgebraStageMap (hBC : B ≤ C) : Spec C ⟶ Spec B` the maps induced by
  subalgebra inclusions.
  - `exists_affineBase_iso`: every test with affine underlying scheme is
    isomorphic in `Over (Spec R)` to `affineBase R A` with `A = Γ(T, ⊤)`.
  - `isNoetherian_affineBase`: `Spec B` is noetherian for a finitely generated
    subalgebra `B` of `A`, when `R` is noetherian (Hilbert basis theorem,
    `isNoetherianRing_of_fg`).
  - `exists_stage_lineBundle` (`f` quasi-compact and quasi-separated): every line
    bundle `M` on `X ×_{Spec R} Spec A` is isomorphic to the pullback of a line
    bundle on `X ×_{Spec R} Spec B`, for some finitely generated `R`-subalgebra
    `B` of `A`. This is the Library theorem
    `NoetherianApproximation.lineBundleSubalgebraDescent`, applied to the base
    change square of `f` along `Spec A ⟶ Spec R` and transported through the
    symmetry isomorphism `relativeSpaceSymmetry` between the two orders of the
    fibre product.
  - `exists_stage_pullback_iso` (`f` quasi-compact and quasi-separated): if two
    line bundles on `X ×_{Spec R} Spec B` (`B` finitely generated) become
    isomorphic over `Spec A`, they become isomorphic over `Spec C` for some
    finitely generated `C` with `B ≤ C`. This is the Library theorem
    `NoetherianApproximation.lineBundleIsoSubalgebraDescent`, applied over the
    base `Spec B` to the cartesian squares `relativeProjection_isPullback`. Its
    `B`-subalgebra of `A` is turned into an `R`-subalgebra containing `B` by
    `Subalgebra.fg_restrictScalars_and_le_of_fg`.
- Section `Bijective`, with the hypotheses of the main theorem and with `ξ`
  such that `g ↦ F.map g.op ξ` is bijective on every noetherian affine test:
  - `bijective_affineBase`: the map is bijective on `affineBase R A` for every
    `R`-algebra `A`.
    *Injectivity.* Let `g₁, g₂ : Spec A ⟶ P` have the same image. Because `P` is
    locally of finite presentation, each `gᵢ` factors through `Spec Bᵢ` for some
    finitely generated subalgebra `Bᵢ` (Library
    `exists_affinePoint_subalgebra`). Hence both factor through
    `Spec (B₁ ⊔ B₂)`, as `qᵢ`. Represent the images of `ξ` under `qᵢ` by rigidified
    line bundles `rᵢ` (`exists_rigidified_sheafClassOf`). Their classes agree over
    `Spec A`, so their pullbacks to `Spec A` are isomorphic
    (`nonempty_pullback_iso_of_map_eq`). Then they are already isomorphic over
    some finitely generated `C ≥ B₁ ⊔ B₂` (`exists_stage_pullback_iso`). So the
    restrictions of `q₁` and `q₂` to `Spec C` have the same image. `Spec C` is a
    noetherian affine test, so these restrictions are equal by injectivity there.
    Composing with `Spec A ⟶ Spec C` gives `g₁ = g₂`.
    *Surjectivity.* Represent a section `x` over `Spec A` by a rigidified line
    bundle `r`. Descend its underlying line bundle to some finitely generated `B`
    (`exists_stage_lineBundle`). By surjectivity on the noetherian affine test
    `Spec B`, its class is the image of `ξ` under some `p : Spec B ⟶ P`. Then
    `Spec A ⟶ Spec B ⟶ P` maps `ξ` to `x`, by `map_sheafClassOf` and
    `sheafClassOf_eq_of_iso`.
  - `bijective_of_isAffine`: the map is bijective on every test with affine
    underlying scheme, by `exists_affineBase_iso` and `bijective_of_iso`.

## Provenance

The argument is the standard reduction of representability over a noetherian
base to locally noetherian (here: noetherian affine) test schemes. On the
functor-of-points side it uses that `Hom_S(-, P)` commutes with filtered limits of
affine schemes when `P` is locally of finite presentation (Stacks Project, Tag
01ZC). On the Picard side it uses that line bundles and their isomorphisms
descend to finitely generated stages (Stacks Project, Lemmas 32.10.3, tag 0B8W,
and 32.10.2, tag 01ZR, as recorded in the Markdown of the Library module
`NoetherianApproximation.LineBundleDescentStatements`; used here through the
Library theorems cited above). The Lean route is internal to this
development: it uses the Library's published approximation results named above
rather than a general limit-preservation theorem for the class sheaf.
