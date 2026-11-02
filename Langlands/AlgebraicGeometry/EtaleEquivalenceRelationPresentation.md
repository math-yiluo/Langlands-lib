# Étale equivalence relations from presheaf kernel pairs

Authors: Worker 239 and Worker 266. Worker 239 wrote the Lean module and the
first version of this Markdown. Worker 266 checked both against the sources,
removed an unneeded elaboration option and revised the citations.

This helper module links the Library's algebraic spaces over a base scheme
`S` (fppf sheaves on `Over S` with values in `Type (u + 1)`, from
`Langlands.AlgebraicGeometry.AlgebraicSpace.Basic` and `SchemeLocalGeometry`)
to the absolute étale equivalence relations of
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation`. It supplies the
lemmas used by the transfer proof
`EtaleEquivalenceRelationAffineDescentTransferProof`. It imports the
published definitions unchanged and adds no axioms. Throughout, `schemeYoneda S`
is the Library's lifted Yoneda embedding of `Over S` into presheaves, and
`IsEtale`, `IsSurjective` and `AlgebraicSpace.IsFinite` are the Library's
representable-morphism properties: every represented base change is an actual
scheme morphism with the property.

## Provenance

The mathematics is the standard passage between an algebraic space and a
presentation, from the registered source
`stacks-etale-equivalence-relations-2026-11-01` (directory SHA-256
`df1ecbfa63c5e31cf736d9ea79dd262976c3098fd9b36f2dd32668d44bf75420`):
`0263.html` (Definition 65.9.3: a presentation is `U`, `R = U ×_F U` and an
étale surjection `U → F`), `03C5.html` (Lemma 39.20.3: a morphism `U → M`
that equalizes `s` and `t`, induces a surjection of `τ`-sheaves
`h_U → h_M`, and for which `R → U ×_M U` induces a surjection of
`τ`-sheaves, makes `M` represent the quotient sheaf `U/R`), and `0APD.html`
and `07S3.html` (Definition 39.21.1 of cartesian morphisms and Lemma 39.20.7).

Two further registered sources are cited:

- `stacks-groupoid-schemes-chapter-pdf-2026-07-14`, the Groupoid Schemes
  chapter PDF built on 14 July 2026 (file SHA-256
  `4506a39201063afc270cbb68c9c0c1d3c90937c03f98cfee074605b402e7a30f`). On
  PDF p.39, the sentence just before Lemma 39.20.3 says that the lemma applies
  "for example if τ = fppf, U → M is flat, of finite presentation and
  surjective, and R ≅ U ×_M U". This sentence is not on the tag page.
- `stacks-fppf-covering-021m-2026-11-01`, the tag page of
  [Definition 34.7.1](https://stacks.math.columbia.edu/tag/021M), downloaded
  on 1 November 2026 (directory SHA-256
  `4ccbd8bcf3d37f25e74d72cf78a921c81946155c473096270dcd9b12ddf732a9`): an
  fppf covering of `T` is a family of morphisms `T_i → T` that are flat and
  locally of finite presentation and are jointly surjective. So a flat,
  locally finitely presented surjection already gives a surjection of fppf
  sheaves, and the lemmas below assume local finite presentation only.

The source for the finite-surjective statement itself is
`stacks-algebraic-space-affine-descent-2026-11-01` (`07VQ.html`, directory
SHA-256 `10fa51455958afc737851009364630c6f8e05ff49d790473a03fa1baaa4c00a0`).
In the first paragraph of the proof of Lemma 70.15.1 (Tag 07VS), the target
`Y` is quasi-compact because `f` is surjective and `X` is quasi-compact. The
Lean proof does not use quasi-compactness of algebraic spaces. To choose
finitely many affine charts, `exists_affine_atlas` uses the quasi-compactness
of the affine scheme `V` that maps surjectively to `Y`.

The Lean formulations below are derived for this route. They are not stated
in this form in the literature, and the proofs are internal.

## Fppf local surjectivity and representation

- `AlgebraicSpace.mem_fppfTopology_of_mem`: a sieve on `T : Over S` that
  contains a morphism `p : T' ⟶ T` whose underlying scheme morphism is flat,
  locally of finite presentation and surjective is an fppf covering sieve.
  The proof uses Mathlib's `singleton_mem_fppfPrecoverage` and the
  description of the slice topology `GrothendieckTopology.mem_over_iff`.
- `AlgebraicSpace.isLocallySurjective_of_isEtale`: an étale surjective map
  `a` from a represented scheme to a presheaf is locally surjective for the
  fppf topology. Each section `y` over `T` lifts to the represented base
  change of `a` along `y`, whose projection to `T` is étale and surjective.
- `AlgebraicSpace.isLocallySurjective_map`: the represented map of a flat,
  locally finitely presented, surjective `q : U ⟶ M` is locally surjective,
  by base change of these three properties.
- `AlgebraicSpace.nonempty_iso_of_isPullback`: let `Y` be an fppf sheaf and
  `a : schemeYoneda U ⟶ Y` locally surjective, with represented kernel pair
  `(t, s) : R ⟶ U` (an `IsPullback` square of presheaves). Let
  `q : U ⟶ M` be flat, locally of finite presentation and surjective, with
  `(t, s)` a pullback of `q` along itself in `Over S`. Then
  `schemeYoneda M ≅ Y`. The proof works in the category of fppf sheaves. Both
  `a` and the sheaf map of `q` are locally surjective, hence regular
  epimorphisms (Mathlib's `IsRegularEpiCategory` for sheaves of types). Both
  are therefore coequalizers of their common kernel pair
  (`isColimitCoforkOfEffectiveEpi`), and the two coequalizer points are
  isomorphic. This is the form of Lemma 39.20.3 used here.

## Atlases and kernel pairs

- `AlgebraicSpace.isStableUnderBaseChange_inverseImage_forget` (instance): a
  property of scheme morphisms stable under base change remains so for
  morphisms of `Over S`.
- `AlgebraicSpace.exists_preimage_of_isPullback`: in a pullback square of
  schemes over `S`, two points with the same image lift to a point of the
  pullback.
- `AlgebraicSpace.isPullback_of_map`: the represented functor reflects
  pullback squares, since it is faithful.
- `AlgebraicSpace.isEtale_map`: the represented map of an étale morphism is
  étale (Mathlib's `MorphismProperty.relative_map`).
- `AlgebraicSpace.IsEtale.comp`: étale maps of presheaves compose.
- `AlgebraicSpace.isSurjective_of_isPullback`: a representable map
  `a : schemeYoneda U ⟶ Y` is surjective if, for a surjective
  `c : schemeYoneda V ⟶ Y`, some represented pullback `W` of `a` along `c`
  has a surjective projection `p : W ⟶ V`. A point of a test scheme `T` is
  lifted first to `T ×_Y V`, then to `W` over `V`, and finally to
  `T ×_Y U` by the universal property.
- `AlgebraicSpace.exists_affine_atlas`: if `Y` has an étale surjective map
  `a` from a scheme `U` and a surjective map `c` from an affine scheme `V`,
  then it has an étale surjective map from an affine scheme. The images in
  `V` of the preimages of the affine charts of `U` form an open cover of `V`,
  via the étale (hence open) surjective projection of the pullback of `a`
  along `c`. A finite subcover exists because `V` is quasi-compact. The
  disjoint union `U₀` of the corresponding finitely many charts is affine. Its
  map to `U` is étale (`IsZariskiLocalAtSource.sigmaDesc`), so the composite
  `U₀ → Y` is étale. It is surjective by the previous lemma, since the
  chosen charts cover `V`.
- `AlgebraicSpace.exists_kernelPair`: an étale map from a scheme to a
  presheaf has a represented kernel pair `(t, s) : R ⟶ U` whose projections
  have étale underlying scheme morphisms.

## The relation and its quotient

In namespace `EtaleEquivalenceRelation`, for `a : schemeYoneda U ⟶ Y` with
represented kernel pair `(t, s) : R ⟶ U`:

- `exists_lift_of_isPullback` and `hom_ext_of_isPullback`: two morphisms
  `T ⟶ U` with equal images in `Y` lift to `T ⟶ R`, and morphisms to `R`
  are determined by their two projections.
- `ofKernelPair t s a h ht hs`: the étale equivalence relation with
  `U := U.left`, `R := R.left`, `t := t.left` and `s := s.left`. The map
  `R.left ⟶ U.left ⨯ U.left` into the absolute product is a monomorphism
  because morphisms to `R` are determined by their projections. Reflexivity,
  symmetry and transitivity on points of arbitrary schemes follow from the
  lifting lemma. Each such point is viewed as a scheme over `S` through `U` or
  `R`.
- `ofKernelPair_hasFiniteSurjectiveCoverWithAffineQuotient`: suppose `a` is
  étale and surjective, and `c : schemeYoneda V ⟶ Y` is finite and
  surjective with `V` affine. Then `ofKernelPair t s a h ht hs` satisfies
  `HasFiniteSurjectiveCoverWithAffineQuotient`. With `φ : U' ⟶ U` and
  `q : U' ⟶ V` the projections of the represented pullback of `a` along `c`,
  the cover is `ofKernelPair` of the pullback of `q` along itself. Its first
  component `φ.left` is finite and surjective by base change of `c`. Its
  second component `g` is the lift of `(pr₁ ≫ φ, pr₂ ≫ φ)` to `R`. The pair
  is a cartesian morphism: `g ≫ t = pr₁ ≫ φ`, and the square
  `(g, pr₂, s, φ)` is a pullback by pasting of pullback squares of presheaves
  and `isPullback_of_map`. The cover has the affine quotient `V` through
  `q.left`. That map is étale and surjective, hence flat and locally of
  finite presentation, and `U' ×_V U'` is a pullback of schemes. So the
  morphism of relations induced by `φ : U' → U`, the base change of `c`,
  satisfies the cartesian hypothesis of Lemma 39.20.7 (Definition 39.21.1,
  `0APD.html`).
- `exists_isAffine_iso_of_hasAffineQuotient`: if `Y` is an fppf sheaf, `a`
  is étale and surjective, and `ofKernelPair t s a h ht hs` has an affine
  quotient `q : U.left ⟶ M`, then some `M' : Over S` with `IsAffine M'.left`
  satisfies `schemeYoneda M' ≅ Y`. The quotient map `q` is flat, locally of
  finite presentation and surjective, hence an effective epimorphism of
  schemes (Mathlib's instance in `Sites.Fpqc`). The structure map of `U`
  coequalizes the kernel pair of `q`, because `t` and `s` are maps over `S`,
  so it descends to `m : M ⟶ S`. Put `M' := Over.mk m`. The square is a
  pullback in `Over S` because the forgetful functor reflects it. Then
  `nonempty_iso_of_isPullback` gives the isomorphism.

## Implementation notes

In this Mathlib version, two instances are not found by instance search. For
`IsStableUnderComposition` of the étale-relative property, `IsEtale.comp`
is elaborated with
`set_option backward.isDefEq.respectTransparency.types false`. This is the
only declaration with that option. For `IsZariskiLocalAtSource @Etale`,
`exists_affine_atlas` supplies the explicit term
`HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)`. The option
affects only elaboration; the kernel checks every proof.
