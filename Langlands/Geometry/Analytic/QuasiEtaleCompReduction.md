# Composition of quasi-étale morphisms from local domain–étale factorizations

This module proves `quasiEtaleCompReduction : QuasiEtaleCompReductionStatement.{u, v} K`
(module `QuasiEtaleCompPrerequisites`). Assume two statements:

- (A) `QuasiEtaleLocalDomainFactorizationsStatement` (module
  `QuasiEtaleLocalDomainFactorizationsStatement`): every
  quasi-étale morphism has local domain–étale factorizations;
- (B) `EtaleDomainQuasiEtaleStatement`: an étale morphism into an analytic
  domain, followed by the inclusion of the domain, is quasi-étale.

Then quasi-étale morphisms of `LocalizedCategory.{u, v, v} (K := K)` are
stable under composition (`QuasiEtaleCompStatement`). No other assumption is
made. Étale base change along a domain inclusion is used, and it is the
Library theorem `localizedEtalePullbackBaseChange`.

## Notation

For a morphism `f : U ⟶ X`, `HasDomainEtaleFactorization f` means
`f = j ≫ g`, where `g : W ⟶ X` is étale and `j : U ⟶ W` is an
analytic-domain embedding (`IsAnalyticDomainEmbedding`). An analytic-domain
embedding is an isomorphism onto `domainObj W D` followed by the inclusion
`domainι W D`, for an analytic domain `D` of `W`.
`HasLocalDomainEtaleFactorizations f` asks, at every point `y` of `U`, for a
finite set of analytic domains of `U` that all contain `y`, whose union is a
neighbourhood of `y`, and on each of which `f` has a domain–étale
factorization. The Library shows that this implies `quasiEtale f`
(`HasLocalDomainEtaleFactorizations.quasiEtale`).

## Lemmas

1. `etale_domainPreimageMap`. Let `w : W ⟶ X` be étale and `D` an analytic
   domain of `X`. Then the restriction `domainPreimageMap w D` from the
   preimage domain `w⁻¹(D)` to `D` is étale. The Library square
   `domainPreimage_isPullback` is a pullback of `w` along `domainι X D`.
   `localizedEtalePullbackBaseChange` gives another pullback whose
   projection is étale. The two pullbacks are isomorphic, and étaleness is
   invariant under isomorphism (`cancel_left_of_respectsIso`).
2. `HasDomainEtaleFactorization.comp_etale` and
   `HasLocalDomainEtaleFactorizations.comp_etale`: composing with an étale
   morphism `h` keeps these properties. The new étale envelope map is
   `g ≫ h`, étale by `etale_comp`.
3. `HasDomainEtaleFactorization.subspaceExtend`. Let `E` be an analytic
   domain of the domain `domainObj U P`, and let `P.subspaceExtend E` be its
   image in `U`. Then a domain–étale factorization of `f` on `E` gives one on
   `P.subspaceExtend E`. The Library isomorphism `domainNestedLocalizationIso`
   identifies the two domain objects compatibly with their inclusions, and
   domain–étale factorizations move along isomorphisms (`iso_comp`).
4. Local factorizations of `f` restrict to every analytic domain `Q` of `U`.
   This is the Library theorem `HasLocalDomainEtaleFactorizations.domainι_comp`
   (module `CompactQuasiEtaleDiagonalPullbacks`), imported here and not
   reproved.
5. `IsAnalyticDomainEmbedding.of_comp_domainι`. Let `n : V ⟶ domainObj W P`
   be such that `n ≫ domainι W P` is an analytic-domain embedding, with image
   the domain `D` of `W`. Then `n` is an analytic-domain embedding. Every
   point of `D` is the image of a point of `V`, so `D ≤ P`. Then `D`,
   restricted to `P`, is a domain `D'` of `domainObj W P` with
   `P.subspaceExtend D' = D`. The nested-domain isomorphism and an
   `eqToIso` give the isomorphism from `V` to `domainObj (domainObj W P) D'`.
   The required equation follows after cancelling the monomorphism
   `domainι W P`.
6. `HasLocalDomainEtaleFactorizations.analyticDomainEmbedding_comp`: local
   factorizations persist after precomposition with an analytic-domain
   embedding. This is lemma 4 followed by the Library's transport along
   isomorphisms (`HasLocalDomainEtaleFactorizations.of_iso`).
7. `HasLocalDomainEtaleFactorizations.of_domain_cover`. Suppose every point
   `y` of `U` has a finite set of analytic domains, all containing `y`,
   whose union is a neighbourhood of `y`, and on each of which the
   restriction of `f` has local factorizations. Then `f` has local
   factorizations. At `y`, for each member `D`, the local factorizations of
   the restriction at `y` give a finite family of domains of `D`. Their
   images in `U` (lemma 3) cover `O ∩ D` for some neighbourhood `O` of `y`
   in `U`. The new family is the union of these finitely many families. It
   covers the intersection of the given neighbourhood with the finitely many
   sets `O`, which is a neighbourhood of `y`.

## The local step

`hasLocalDomainEtaleFactorizations_inf_domainPreimage` assumes (A) and (B).
Let `f : A ⟶ B` and `g : B ⟶ C`, let `D` be an analytic domain of `A` and `E`
one of `B`. Suppose `f` restricted to `D` and `g` restricted to `E` have
domain–étale factorizations. Then `f ≫ g` restricted to
`G = D ⊓ f⁻¹(E)` has local factorizations. The proof goes as follows.

- Write `domainι A D ≫ f = j ≫ w`, with `w : W ⟶ B` étale and `j` an
  analytic-domain embedding. Write `domainι B E ≫ g = e'.hom ≫ domainι W' R ≫ w'`,
  with `w' : W' ⟶ C` étale, `R` an analytic domain of `W'`, and `e'` an
  isomorphism from `domainObj B E` to `domainObj W' R`.
- Let `P = w⁻¹(E)`, a domain of `W`, and `p = domainPreimageMap w E`. By
  lemma 1, `p` is étale, so `p ≫ e'.hom` is étale. By (B),
  `p ≫ e'.hom ≫ domainι W' R` is quasi-étale. By (A) it has local
  factorizations, and by lemma 2 so does its composite with `w'`. That
  composite equals `domainι W P ≫ w ≫ g`.
- Let `m : domainObj A G ⟶ domainObj A D` be the order map of `G ≤ D`. It
  is an analytic-domain embedding by lemma 5. The composite `m ≫ j` maps
  into `P`, because `j ≫ w` is `f` on `D` and `G` lies in `f⁻¹(E)`. So it
  lifts to `n : domainObj A G ⟶ domainObj W P` with
  `n ≫ domainι W P = m ≫ j` (`domainLift`). `m ≫ j` is an analytic-domain
  embedding, so lemma 5 shows that `n` is one too.
- By lemma 6, `n ≫ domainι W P ≫ w ≫ g` has local factorizations. This
  morphism equals `domainι A G ≫ f ≫ g`.

## The reduction

`quasiEtaleCompReduction`: let `f : A ⟶ B` and `g : B ⟶ C` be quasi-étale.
It suffices to show that `f ≫ g` has local factorizations
(`HasLocalDomainEtaleFactorizations.quasiEtale`), and lemma 7 reduces this
to a cover. At a point `y` of `A`:

- (A) for `f` at `y` gives a finite family `C_D` of domains of `A`;
- (A) for `g` at `f(y)` gives a finite family `C_E` of domains of `B`.

The cover is the finite family of the domains `D ⊓ f⁻¹(E)` for `D ∈ C_D` and
`E ∈ C_E`. Each contains `y`. Their union contains the intersection of the
neighbourhood `⋃ C_D` with the preimage under the continuous map `f` of the
neighbourhood `⋃ C_E`. On each member the local step applies.

## Relation to the source

Berkovich 1994, Lemma 3.1(i) (registered as
`berkovich-1994-vanishing-cycles-formal-schemes`, printed p.544) states the
composition clause with a one-line proof: it follows from the properties of
étale morphisms and from Theorem 3.4.1 of Berkovich 1993. This module is the
internal assembly of that argument from the two named premises. The use of
Theorem 3.4.1 is isolated in (B). The condition that every domain of a local
family contains the point is isolated in (A); the source's definition does
not ask for it.

## Hausdorff sources

The proof above uses (A) three times: for `f` at `y`, for `g` at `f(y)`, and
in the local step for the quasi-étale morphism with source `domainObj W P`,
where `P = w⁻¹(E)` is a domain of the étale envelope `W` of a factorization
of `f`. When `A` and `B` are Hausdorff, the Library theorem
`hasLocalDomainEtaleFactorizations_of_quasiEtale` (module
`QuasiEtaleDomainLocality`) covers the first two uses. It does not cover the
third, because `W` need not be Hausdorff. The module
`QuasiEtaleHausdorffCompReduction` first shrinks the envelope to a Hausdorff
open subset, which is possible because every Library space is locally
Hausdorff. Its theorem `quasiEtale_comp_of_t2Space` proves composition for
Hausdorff `A` and `B` from (B) alone.

## The general case

This module and the modules it imports do not prove (A) for a source that is
not Hausdorff. In Berkovich's definition (1994, printed p.543), the affinoid
domains `V₁, …, Vₙ` whose union is a neighbourhood of `y` need not contain
`y`. In a Hausdorff space a compact domain missing `y` is closed and can be
dropped. In general it can accumulate at `y`. Example: glue two closed discs
of radius two along the complement of the closed unit disc, and let `y` be
the Gauss point of radius one in the first copy. The unit disc of the first
copy and the whole second copy cover the glued space. The second copy misses
`y`, and the unit disc is not a neighbourhood of `y`. The Markdown of
`QuasiEtaleCompactRefinementsObstruction` describes this space.

Two sources bear on (A) for a source that is not Hausdorff. Neither is
formalized here.

- Ducros, *Families of Berkovich spaces*, Astérisque 400 (2018), registered as
  `ducros-2018-families-berkovich-spaces`. In 5.4.10 Ducros recalls
  Berkovich's definition: `y` has a compact analytic neighbourhood
  `V₁ ∪ … ∪ Vₙ`, where each `Vᵢ` is an affinoid domain of the source that is
  isomorphic over the target to an affinoid domain of an étale space. The
  union is a neighbourhood of `y`, and an individual `Vᵢ` may omit `y`.
  Lemma 5.4.11 (printed pp.120–121 of arXiv:1107.4259v6) proves this notion
  equivalent at each point to Ducros's own notion of quasi-étaleness, which is
  local at a point for the analytic domains containing it (5.2.10). The
  implication from Ducros's notion to Berkovich's starts from a finite union
  of affinoid domains through `y` that is a neighbourhood of `y`. On each
  piece it applies Ducros's Theorem 5.4.6. That theorem characterizes
  quasi-smoothness at a point, for morphisms of good spaces, by an affinoid
  neighbourhood of the point that is isomorphic over the target to an affinoid
  domain of a smooth space. Its proof uses the analytic Zariski Main Theorem,
  cited there as [Duc07b], Theorem 3.2. Separately, the proof of Lemma 5.4.11
  uses Berkovich 1993, Theorem 3.4.1, to extend finite étale covers of germs
  from an affinoid domain of the target to the target itself.
- Berkovich's proof of Lemma 3.1 (1994, printed p.544) says only that the
  lemma follows from the properties of étale morphisms and from Berkovich
  1993, Theorem 3.4.1, on finite étale germs. A proof along these lines would
  use that theorem to glue the étale envelopes near `y` with those near the
  points of the other domains that cannot be separated from `y`. The source
  gives no details.

Statement (B) rests on the same theorem, through Corollary 3.4.2; see the
Markdown of `QuasiEtaleCompPrerequisites`.
