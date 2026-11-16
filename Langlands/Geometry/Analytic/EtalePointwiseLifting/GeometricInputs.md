# Geometric inputs and fraction transport for pointwise étale lifting

Author: Worker 271.

This module isolates two geometric prerequisites and proves that they imply
`EtalePointwiseLiftingStatement` for the actual analytic étale site. The two
prerequisites are unproved propositions. The conditional reduction does not
establish the unconditional target.

## Exact geometric statements

Throughout, `K : Type u` is a complete ultrametric normed field. The field
universe `u` and space and atlas-index universe `v` are independent.

`LocalizedEtaleStabilityStatement K` is the conjunction of two properties
of the published predicate `etale` on `LocalizedCategory.{u, v, v}`:

- Composable étale arrows have étale composite.
- If `g` and `f ≫ g` are étale, then `f` is étale.

The second clause quantifies over arbitrary localized `f`. In particular,
every arrow over `X` between two étale objects over `X` is then étale.
Neither clause is introduced as an instance or an axiom.

`StrongEtalePointwiseBaseChangeStatement K` quantifies over arbitrary
saturated presentations `A`, `B`, and `C`, strong maps `f : A ⟶ C` and
`g : B ⟶ C`, and ordinary points `x` and `y` with equal images. It assumes
that the localized image of `f` is étale. It asks for a saturated
presentation `T` in the same space and index universe, strong maps
`p : T ⟶ A` and `q : T ⟶ B`, and a point `t` of `T` satisfying:

- `p ≫ f = q ≫ g` in the strong-map category;
- the localized image of `q` is étale;
- `p.baseMap t = x` and `q.baseMap t = y`.

There is no Hausdorff assumption, restriction on `g`, universal property,
or demand for a global fibre-product object. The witnesses can depend on
the two points. The étale hypothesis uses precisely the existential
localized predicate from `EtaleSite`, not a newly substituted strong-map
predicate. Establishing that hypothesis's geometric consequences remains
part of proving the prerequisite.

`EtalePointwiseLiftingGeometricInputsStatement K` is the conjunction of
these two named propositions.

## Implemented fraction transport

`exists_localized_etale_pointwise_square_of_strong` assumes the strong
base-change statement and proves its localized-arrow counterpart. It
imposes no site or structure-map condition on the three localized
objects.

First, the object bijection writes all three objects as images of
saturated presentations. The published right-fraction calculus writes
`f` and `g` with quasi-isomorphism denominators `s` and `r` and strong
numerators `f₀` and `g₀`. Precomposing `f` with the isomorphism given by
`s` shows that the localized numerator `f₀` is étale, using the already
proved isomorphism invariance of `etale`.

The original denominator homeomorphisms send the prescribed points
back to the fraction sources. The published formula
`localizedSpaceFunctor_map_rightFraction` shows that these points have
equal images under `f₀` and `g₀`. Apply the strong base-change input to
obtain `T`, `p₀`, `q₀`, and `t`. The desired localized projections are
`L(p₀) ≫ L(s)` and `L(q₀) ≫ L(r)`. In their composites with the
fractions, the denominator isomorphisms cancel; functoriality transports
the strong commuting equation to the required localized equation.
Postcomposition with the denominator isomorphism preserves étaleness
of the second projection. The inverse homeomorphism identities give
the two exact prescribed point images.

This proof uses equality of full strong maps and functoriality, not
faithfulness of the underlying-space functor.

## Implemented site assembly

`etale_site_arrow_of_stability` applies right cancellation to
`f.left ≫ W.hom = U.hom`, where both structure maps are étale.

`etalePointwiseLifting_of_geometricInputs` applies the localized square
construction to the two underlying site arrows. If its second projection
is `q : T ⟶ V.left`, composition stability makes `q ≫ V.hom` étale.
`MorphismProperty.Over.mk` therefore constructs an actual object of
`EtaleSite X`. The square and the two original over-category equations
show that the first projection is also over `X`; `Over.homMk`
constructs both site morphisms. Extensionality for these morphisms
transports the localized commuting equation to equality in the site.
The prescribed point equalities are definitionally those of
`EtaleSite.points X`.

The conclusion has independent universes and no Hausdorff, compactness,
or supplied categorical-pullback assumption. Its geometric inputs remain
explicit premises.

## Provenance

This is a derived interface and categorical reduction, not a verbatim
transcription of a numbered literature result. Its inputs combine the
following geometric facts with the Library's strong-map presentation:

- Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
  (1993), Corollary 3.3.8, printed p.63 / PDF p.60, states preservation
  of étale morphisms under composition and arbitrary base change.
- Corollary 3.3.9 and its graph proof, printed pp.63–64 / PDF pp.60–61,
  give étaleness of a quasifinite morphism whose composite is étale
  and whose postfactor is unramified. The text immediately deduces that
  all morphisms of `Ét(X)` are étale. Our unrestricted localized
  cancellation input also requires justifying quasifiniteness of the
  prefactor or using the graph argument directly; that justification
  is not asserted to be proved here.
- The published `FibreProduct.exists_point` in
  `Langlands.Geometry.Analytic.FibreProductPoints` supplies compatible
  point lifting in the glued chart-system space. It is a partial input
  toward the strong base-change statement, which additionally requires
  a saturated object in universe `v`, strong projections and étaleness.

The original source is registered as `berkovich-1993-etale-cohomology`,
SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The narrower Hausdorff equal-universe `EtaleBaseChangeStatement` is
neither assumed nor proved. It alone would not supply these inputs.
