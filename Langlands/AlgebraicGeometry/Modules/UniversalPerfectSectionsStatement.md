# Universal perfect representatives of actual derived sections

The Prop-valued declaration
`Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsStatement.{u}`
states the objectwise perfect proper direct-image and arbitrary affine
base-change result for an actual line bundle on a smooth proper family.
This file supplies a statement, with no proof of that proposition.
Worker 1013 prepared this pair using Worker 606's shared statement design;
Worker 606 is a coauthor.

## Complete statement and conventions

For every `R : CommRingCat.{u}`, `X : Scheme.{u}`, and
`f : X ⟶ Spec R`, the proposition has hypotheses `Smooth f` and
`IsProper f`. For every `L : Langlands.AlgebraicGeometry.Picard.LineBundle X`,
it asserts the existence of one
`K : CochainComplex (ModuleCat.{u} R) ℤ` with all three properties below.

1. `Langlands.Cohomology.ModuleComplex.IsStrictlyPerfect K`: there are
   integers `a,b` with `K.IsStrictlyGE a` and `K.IsStrictlyLE b`, and for
   every integer `i`, both `Module.Finite R (K.X i)` and
   `Module.Projective R (K.X i)` hold. These are bounds on actual nonzero
   terms, rather than only on cohomology.
2. There is an actual derived-category isomorphism, asserted by
   `Nonempty`, from `DerivedCategory.Q.obj K` to
   `DerivedCategory.Plus.ι.obj
   ((Langlands.Cohomology.DerivedPlus.derivedComplex
   (DerivedSections.relativeGlobalSections f)).obj L.obj)`.
3. For every `T : CommRingCat.{u}` and `φ : R ⟶ T`, there is an actual
   derived-category isomorphism, again asserted by `Nonempty`, from
   `DerivedCategory.Q.obj
   ((Langlands.Cohomology.ModuleComplex.baseChange φ.hom).obj K)` to
   `DerivedCategory.Plus.ι.obj
   ((Langlands.Cohomology.DerivedPlus.derivedComplex
   (DerivedSections.relativeGlobalSections
   (pullback.snd f (Spec.map φ)))).obj
   ((Scheme.Modules.pullback (pullback.fst f (Spec.map φ))).obj L.obj))`.

The last object uses the actual scheme fiber product
`pullback f (Spec.map φ)`, its projection `pullback.snd` to `Spec T`,
and its projection `pullback.fst` to `X`. The coefficient is the usual
module pullback of `L.obj`; `LineBundlePullback` proves that this remains
locally free of rank one. The one existential `K` precedes all `T,φ`.
The unextended comparison in item 2 is explicit, so no identity-base-change
comparison is implicit in the formulation.

Ring, scheme and module carriers lie in arbitrary universe `u`. The file
locally selects Mathlib's `HasDerivedCategory.standard`. In particular the
actual module derived categories have morphism universe `u + 1`; no small
localization is assumed. There are no noetherian, reducedness, projectivity,
connectedness or base-point premises.

## Actual right-derived sections and scalars

The imported published functor
`Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeGlobalSections f`
is exactly `Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor`.
It takes actual structure-sheaf modules on `X` to actual `R`-modules.
The `R`-action on global sections is restriction along
`(Scheme.ΓSpecIso R).inv ≫ f.appTop : R ⟶ Γ(X, ⊤)`.
Thus it uses the canonical identification of the global sections of
`Spec R` with `R`, with the ring map oriented from `R` to `Γ(X, ⊤)`.
After base change the same convention uses the structure map
`pullback.snd f (Spec.map φ)` and scalars in `T`.

The statement applies the published
`Langlands.Cohomology.DerivedPlus.derivedComplex` directly to this functor,
then includes its value in the unbounded derived category with
`DerivedCategory.Plus.ι`. For an additive functor `F`, `derivedComplex F`
is `DerivedCategory.Plus.singleFunctor _ 0 ⋙ F.rightDerivedFunctorPlus`.
Hence geometric cohomology is defined independently of `K`.

For any actual injective resolution `I` of the coefficient module,
`DerivedPlus.derivedComplexIso F I` identifies that derived object with
`DerivedCategory.Plus.Q.obj
(F.mapCochainComplexPlus.obj (DerivedPlus.resolutionPlus I))`.
Applying `DerivedCategory.Plus.ι` and composing with
`DerivedCategory.Plus.QCompιIso` identifies the unbounded object in the
statement with the Q-image of the sections of the integer-indexed
injective resolution. Mathlib supplies enough injectives for `X.Modules`
through its Grothendieck abelian instance, as used in `DerivedSections`;
the statement adds no enough-injectives premise. In nonnegative degrees,
`DerivedPlus.homologyIso` identifies the cohomology with the published
`DerivedSections.relativeCohomology f n`, the actual `rightDerived n`
functor. These generic resolution comparisons are already implemented;
this statement adds no adapter or foundation copy.

The published `ModuleComplex.baseChange φ.hom` is ordinary termwise scalar
extension: its terms are `T ⊗[R] K.X i`, with differentials induced by those
of `K`, using the `R`-action on `T` defined by `φ.hom`. The tensor notation
here describes `ModuleCat.extendScalars φ.hom`; the Lean definition prolongs
that functor to cochain complexes. A bounded complex of projective modules
is K-flat, so such a representative computes derived extension of scalars.
Likewise, a locally free line bundle in degree zero computes its own
derived module pullback. These comparisons justify the ordinary operations
in the source specialization; their geometric and K-flatness proofs remain
obligations for a proof of the proposition. Neither the definition of
`baseChange` nor the present Prop-valued definition proves them.

## Original source and specialization

The registered source is `stacks-perfect-complexes-a04446e5`, folder
SHA-256 `54c831042614714cdb007a024d45dca7f60709efe2c307389ca2ad848b0ccbed`,
at Stacks Project git commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`. Its original file `perfect.tex`
has chapter title *Derived Categories of Schemes*. The registration's
citation metadata incorrectly calls it *More on Flatness*; the source
bytes and citation ID are unchanged.

Worker 1013 read each of the following original statements and complete
proofs, also previously read by Worker 606:

- Lemma 36.30.4 ([tag 0B91](https://stacks.math.columbia.edu/tag/0B91)),
  `lemma-flat-proper-perfect-direct-image-general`, lines 7524–7544:
  perfection and arbitrary base change of proper direct image under the
  indicated finite-presentation and flatness hypotheses.
- Remark 36.30.2 ([tag 0A1I](https://stacks.math.columbia.edu/tag/0A1I)),
  `remark-explain-perfect-direct-image`, lines 7443–7455: one finite
  projective complex computes sections after every affine base-algebra
  change, functorially in that algebra.
- Lemma 36.3.5 ([tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)),
  `lemma-affine-compare-bounded`, lines 236–323: actual derived global
  sections and the exact tilde functor give the affine derived equivalence.
- `lemma-affine-K-flat`, lines 326–342, and
  `lemma-quasi-coherence-pullback`, lines 363–401: K-flat representatives
  and the affine identification of derived scheme pullback with derived
  tensor extension. The intervening pushforward lemma was also read.
- Lemma 36.10.7 ([tag 08EB](https://stacks.math.columbia.edu/tag/08EB)),
  `lemma-perfect-affine`, lines 2418–2432: perfection agrees under the
  affine scheme/module comparison.

Smoothness gives flatness and local finite presentation; properness gives
quasi-compactness and quasi-separatedness, so the family is of finite
presentation as required by 0B91 and 0A1I. An actual line bundle is finite
locally free of rank one. It is therefore perfect in degree zero, finitely
presented as an `𝒪_X`-module, and flat over the base because `f` is flat.
Its support is closed and proper over the base. Thus it meets either case
of 0B91, and also the hypotheses of 0A1I.

The affine equivalence identifies perfect direct image over `Spec R` with
a perfect object of `D(R)`. Choosing one bounded finite projective
representative and applying arbitrary base change gives the displayed
statement. The usual derived-section composition comparison identifies
that direct-image description with the right-derived functor of the
whole section composite used here. Together with the affine derived
pullback comparison and the K-flatness observation above, these are
mathematical proof obligations for the successor proof. The present
statement retains only objectwise existence from the source's functorial
comparisons. This is a specialized statement design derived from the
original, rather than a verbatim transcription of its full generality.

Worker 1013 checked the current four tag pages and available comments on
2026-10-29. The retained supplementary source is
`stacks-universal-perfect-sections-comments-20261029`, folder SHA-256
`cff02c7e0ac074ddd354bad94a42f7c59ebfe956042ad86360bba27b73d7c1d5`.
Its `0B91.html` has comments #4352 and #4499: part (2) does not require the
morphism to be flat, while flatness of the coefficient over the base is
retained. This correction is already in the pinned TeX. The files
`0A1I.html`, `06Z0.html` and `08EB.html` have no comments. No project errata
file for the original source was present in the supplied public locations.

## Scope

This is one objectwise statement unit. It asserts no naturality of chosen
isomorphisms, compatibility with restriction maps, residue-field H1
restriction comparison, Künneth, local two-axis triviality or relative
cube detection. Those remain separate statements and proofs. Neither
this proposition nor local minimal finite free representatives alone
prove local triviality. The imported definitions are published; the
geometric perfect-direct-image and base-change proposition is only stated
here.
