# Statement: quasi-étale arrows have domain–étale factorizations through every point

This module states one proposition and proves nothing. The proposition is
`QuasiEtaleLocalDomainFactorizationsStatement K`, in the namespace
`Langlands.Analytic.SaturatedAtlasPresentation`. Its argument `K : Type u` is
a complete ultrametric normed field.

## The statement

For all objects `U` and `X` of the localized category
`LocalizedCategory.{u, v, v} (K := K)` and every arrow `f : U ⟶ X`: if
`quasiEtale f`, then `HasLocalDomainEtaleFactorizations f`.

The two Library predicates involved are:

- `quasiEtale` (module `QuasiEtaleSite`). It holds for arrows isomorphic in
  the arrow category to `localizationFunctor.map g` for a strong map `g` with
  `IsQuasiEtale g`. That condition at a point `y` of the source asks for a
  finite set of atlas charts whose union is a neighbourhood of `y`, each
  identified compatibly with `g` with an affinoid domain of a space étale over
  the target. The charts need not contain `y`.
- `HasLocalDomainEtaleFactorizations f` (module `QuasiEtaleDomainLocality`).
  For every point `y` of the underlying space of `U`, there is a finite set
  `C` of analytic domains of `U` (elements of `(presentationOf U).AnalyticDomain`)
  with three properties:
  - the union of their carriers is a neighbourhood of `y`;
  - every `D ∈ C` contains `y`;
  - for every `D ∈ C`, the restriction `domainι U D ≫ f` satisfies
    `HasDomainEtaleFactorization`: it is an analytic domain embedding
    followed by an étale arrow.

So the statement says: the pieces in the quasi-étale condition can always be
chosen to pass through the given point. The source `U` is arbitrary. No
Hausdorff, compactness or smallness hypothesis is imposed on `U` or `X`.

## What the Library already proves

- The converse holds for every source:
  `HasLocalDomainEtaleFactorizations.quasiEtale` (module
  `QuasiEtaleDomainLocality`) proves that
  `HasLocalDomainEtaleFactorizations f` implies `quasiEtale f`.
- The statement holds for a Hausdorff source:
  `hasLocalDomainEtaleFactorizations_of_quasiEtale` (same module) proves it
  under `[T2Space (localizedSpaceFunctor.obj U)]`. In a Hausdorff space the
  charts are compact, hence closed, so the charts not containing `y` can be
  dropped.

This module does not prove the general case, with a source that need not be
Hausdorff. The module `QuasiEtaleHausdorffStabilityStatement` states the
clauses of Berkovich's Lemma 3.1 for Hausdorff sources, where the Hausdorff
case above is available in place of this proposition. For instance
`quasiEtaleHausdorffBaseChange` (module `QuasiEtaleHausdorffBaseChangeProof`)
proves base change for a Hausdorff source through
`quasiEtale_of_isPullback_of_t2Space`.

## Provenance

The proposition is derived. It is not transcribed from one numbered
statement. It compares two forms of the quasi-étale condition in Berkovich's
work.

1. Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994),
   registered as `berkovich-1994-vanishing-cycles-formal-schemes`, §3,
   printed p.543 (PDF p.5):

   > Let φ : Y → X be a morphism of k-analytic spaces. We say that φ is
   > quasi-étale if for every point y ∈ Y there exist affinoid domains
   > V₁, …, Vₙ ⊂ Y such that V₁ ∪ … ∪ Vₙ is a neighborhood of y and each Vᵢ
   > can be identified with an affinoid domain in a k-analytic space étale
   > over X.

   This form does not require `y ∈ Vᵢ`. The Library's `IsQuasiEtaleAt`
   follows it. The pointed form is the one Berkovich produces in the proof of
   Proposition 2.3 on the same page. There the formal affine pieces are chosen
   with `y` in every generic fibre, and each generic fibre is shrunk to an
   affinoid neighbourhood of `y`.

2. Berkovich, *Étale cohomology for non-Archimedean analytic spaces*,
   Publ. Math. IHÉS 78 (1993), registered as `berkovich-1993-etale-cohomology`,
   §1.1. On printed p.13 (PDF p.10), a quasinet requires, for each point
   `x`, members `V₁, …, Vₙ` with `x ∈ V₁ ∩ … ∩ Vₙ` and `V₁ ∪ … ∪ Vₙ` a
   neighbourhood of `x`. On printed p.14 (PDF p.11) Berkovich remarks that
   when `X` is Hausdorff it suffices to check that each point has a
   neighbourhood of the form `V₁ ∪ … ∪ Vₙ`. So the nonpointed form is a
   shortcut for Hausdorff spaces. In Berkovich's general (non-Hausdorff)
   setting the pointed form is the basic one.

The proposition says that, for quasi-étale arrows of the Library's localized
category, the 1994 nonpointed form implies the pointed form, as in the
quasinet condition of 1993 §1.1, for every source.

Truth in Berkovich geometry. Ducros, *Families of Berkovich spaces*,
Astérisque 400 (2018), registered as `ducros-2018-families-berkovich-spaces`
(arXiv:1107.4259v6), recalls Berkovich's nonpointed definition in 5.4.10 and
proves in Lemma 5.4.11 (printed pp.120–121) that, at each point, it is
equivalent to his own notion of quasi-étaleness at that point. The two
directions of his proof are the two halves of the proposition.

- From the nonpointed form to his notion, he uses one affinoid domain of the
  family that contains the point. His notion is local at a point for the
  analytic domains containing it (5.2.10, printed p.110, through Jacobian
  presentations).
- From his notion back to affinoid domains, he takes affinoid domains `Vᵢ`
  through the point, with union a neighbourhood. On each he applies his
  Theorem 5.4.6 (printed pp.118–119), a characterization of quasi-smoothness
  for good spaces whose proof uses the analytic Zariski Main Theorem. In the
  quasi-étale case this gives an affinoid neighbourhood of the point in `Vᵢ`
  that is an affinoid domain of a space étale over an affinoid domain `Uᵢ` of
  the target. Berkovich 1993,
  Theorem 3.4.1 (finite étale covers of the germs `(X, x)` and `(Uᵢ, x)` are
  both equivalent to finite étale `𝓗(x)`-algebras) then extends that étale
  space to an open neighbourhood of the image point. The resulting domains
  contain the point.

One might instead try to work directly with the étale envelopes of the given
family, gluing the envelope of a member that misses `y` to the envelope of a
member that contains `y`. If a member `V` misses `y` but accumulates at it,
then, since `V` is compact, some point of `V` cannot be separated from `y`.
That inseparability does not supply the gluing data. Points that cannot be
separated can have different images in the target: in the doubled disc
described below, take `f` to be the identity of the doubled space; the two
Gauss points cannot be separated, and their images are distinct points of
the target. Even when two points have the same
image `x`, the pointed étale germs of their envelopes over the target germ
at `x` need not be isomorphic, since their completed residue fields can be
different finite separable extensions of `𝓗(x)`. Such an approach would have
to find envelopes refined over a common target germ, identify their finite
étale fibres compatibly with the chart maps, and check that the resulting
germ isomorphisms have compatible representatives on the overlaps. Berkovich
1993, Theorem 3.4.1, lifts a compatible isomorphism of fibres to an
isomorphism of germs, but it does not produce those data. This page gives
no argument that produces them, and this module formalizes neither
approach.

## Why the statement is needed

The doubled disc shows that the given nonpointed charts cannot simply be
transported. Glue two closed unit discs along the open unit disc
`{|T| < 1}`, and take the identity of the glued space. At the Gauss point of
the first copy, the whole second copy and the affinoid domain `{|T| = 1}` of
the first copy form a nonpointed family: their union is the whole space, but
the second copy does not contain the point, and `{|T| = 1}` alone is not a
neighbourhood of it. Pull the family back along the
inclusion of the first copy. The second copy becomes the open unit disc,
which is not an affinoid domain, and every affinoid domain inside it lies in
some `{|T| ≤ ρ}` with `ρ < 1`. So no finite union of affinoid domains inside
it, together with `{|T| = 1}`, is a neighbourhood of the Gauss point: points
of radius close to `1` are missed. The Library note
`QuasiEtaleCompactRefinementsObstruction` uses the same doubled-disc
behaviour for a different purpose.

The module `QuasiEtaleBaseChangeReduction` derives
`QuasiEtaleBaseChangeStatement` (Berkovich 1994, Lemma 3.1(i), base change
clause), for every pullback square, from this proposition
(`quasiEtaleBaseChange_of_localDomainFactorizations`). It combines it with
`HasLocalDomainEtaleFactorizations.of_isPullback` and the published étale base
change `localizedEtalePullbackBaseChange`. Other clauses of Lemma 3.1 meet the
same obstruction.

## Universes

`u` is the universe of the field. `v` is the universe of spaces and atlas
indices of `LocalizedCategory.{u, v, v}`. These are the universes of
`QuasiEtaleBaseChangeStatement`.

## Scope

This is a `lean.statement`: nothing is proved here.
