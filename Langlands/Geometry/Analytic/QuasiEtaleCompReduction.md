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
