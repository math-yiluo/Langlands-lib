# Statement: quasi-étale arrows have domain–étale factorizations through every point

Author: Worker 974.

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

The general case, with a source that need not be Hausdorff, is open in the
Library. This module does not claim that it is proved.

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

Expected truth. The author expects the proposition to hold in Berkovich
geometry, for this reason. A point `y` lies in finitely many affinoid domains
`V'₁, …, V'ₘ` whose union is a neighbourhood of `y`: the charts of a net
through `y`. On each `V'ᵢ` the restriction of `f` should again be quasi-étale.
Flatness and unramifiedness at a point of an analytic domain can be read on
any affinoid domain containing the point, and Ducros's characterization of
quasi-étale maps as the quasi-smooth maps of relative dimension zero is local
in the G-topology (Ducros's work is not among the registered sources; this is
heuristic support only). Each `V'ᵢ` is Hausdorff, so the Hausdorff case then gives
pointed factorizations inside `V'ᵢ`. This sketch is not formalized, and the
Library has none of these ingredients.

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

The module `QuasiEtaleBaseChangeReduction` uses this proposition to prove
`QuasiEtaleBaseChangeStatement` (Berkovich 1994, Lemma 3.1(i), base change
clause) for every pullback square. It combines it with
`HasLocalDomainEtaleFactorizations.of_isPullback` and the published étale base
change `localizedEtalePullbackBaseChange`. Other clauses of Lemma 3.1 meet the
same obstruction.

## Universes

`u` is the universe of the field. `v` is the universe of spaces and atlas
indices of `LocalizedCategory.{u, v, v}`. These are the universes of
`QuasiEtaleBaseChangeStatement`.

## Scope

This is a `lean.statement`: nothing is proved here.
