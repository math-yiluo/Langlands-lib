# Composition of quasi-étale morphisms with Hausdorff sources

This module works in the localized category
`LocalizedCategory.{u, v, v} (K := K)` over a complete ultrametric normed
field `K : Type u`. It proves
`quasiEtaleHausdorffCompReduction : QuasiEtaleHausdorffCompReductionStatement.{u, v} K`
(module `QuasiEtaleHausdorffCompReductionStatement`), through the unbundled
theorem `quasiEtale_comp_of_t2Space`. Assume
`EtaleDomainQuasiEtaleStatement K` (module `QuasiEtaleCompPrerequisites`): an
étale morphism into an analytic domain, followed by the inclusion of the
domain, is quasi-étale. Let `f : A ⟶ B` and `g : B ⟶ C` be quasi-étale, and
suppose that `localizedSpaceFunctor.obj A` and `localizedSpaceFunctor.obj B`
are Hausdorff (`T2Space`). Then `f ≫ g` is quasi-étale. No hypothesis is made
on `C`.

`EtaleDomainQuasiEtaleStatement` is a hypothesis of the theorem. This module
does not prove it.

The notation `HasDomainEtaleFactorization` and
`HasLocalDomainEtaleFactorizations` is that of the module
`QuasiEtaleCompReduction`. A domain–étale factorization of `f : U ⟶ X` is
`f = j ≫ w` with `j : U ⟶ W` an analytic-domain embedding and `w : W ⟶ X`
étale. The space `W` is its étale envelope.

## Why the envelope has to be Hausdorff

The module `QuasiEtaleCompReduction` proves composition for arbitrary sources
from two premises: `QuasiEtaleLocalDomainFactorizationsStatement` and
`EtaleDomainQuasiEtaleStatement`. For a Hausdorff source the first premise is
the Library theorem `hasLocalDomainEtaleFactorizations_of_quasiEtale` (module
`QuasiEtaleDomainLocality`). That reduction uses the first premise three
times: for `f` at a point `y` of `A`, for `g` at `f(y)`, and, in the local
step `hasLocalDomainEtaleFactorizations_inf_domainPreimage`, for a quasi-étale
morphism whose source is the domain `w⁻¹(E)` of the étale envelope `W` of a
factorization of `f`. That envelope is not Hausdorff in general. This module
therefore shrinks the envelope to a Hausdorff open subset before the local
step. It uses that every analytic space of the Library is locally Hausdorff:
the field `locallyHausdorff` of `IndexedAffinoidAtlas` gives every point a
Hausdorff neighbourhood.

## Lemmas

1. `HasDomainEtaleFactorization.exists_t2Space_inf_openDomain`. Let `D` be an
   analytic domain of `A`, let `y ∈ D`, and let `domainι A D ≫ f = j ≫ w` be a
   domain–étale factorization with envelope `W`. Then there are an open set
   `O` of `A` containing `y` and a domain–étale factorization of
   `domainι A (D ⊓ openDomain O) ≫ f` whose envelope has a Hausdorff
   underlying space. The proof:
   - `locallyHausdorff` gives a Hausdorff neighbourhood `N` of `j(y)` in `W`.
     Its interior `H` is open and Hausdorff (`IsEmbedding.t2Space` for the
     inclusion).
   - By continuity of `j`, `j⁻¹(H)` is a neighbourhood of `y` in `D`. By
     `mem_nhds_subtype` it contains `D ∩ O₀` for a neighbourhood `O₀` of `y`
     in `A`. Let `O` be the interior of `O₀`.
   - Let `D' = D ⊓ openDomain O` and let `m` be the order map from
     `domainObj A D'` to `domainObj A D`. It is an analytic-domain embedding
     (`IsAnalyticDomainEmbedding.of_comp_domainι`). The composite `m ≫ j`
     maps into `H`, so it lifts (`domainLift`) to
     `n : domainObj A D' ⟶ domainObj W (openDomain H)`. Since `m ≫ j` is an
     analytic-domain embedding, so is `n`.
   - The new envelope is `domainObj W (openDomain H)`, whose underlying space
     is `H`. The new étale map is `domainι W (openDomain H) ≫ w`. It is
     étale: the inclusion of an open domain is étale
     (`etaleOpenDomainStatement`, module `EtaleOpenDomains.Proof`), and
     étale morphisms compose (`etale_comp`). The factorization equation
     follows from `n ≫ domainι W (openDomain H) = m ≫ j` and
     `m ≫ domainι A D = domainι A D'`.
2. `HasLocalDomainEtaleFactorizations.exists_t2Space_envelopes`. If `f` has
   local domain–étale factorizations, then at every point `y` of the source
   the finite family of domains can be chosen so that every factorization
   has a Hausdorff envelope. Apply lemma 1 to each member `D` of the given
   family at `y`. The new family consists of the domains `D ⊓ openDomain O_D`.
   They all contain `y`. Their union contains the intersection of the old
   union with the finitely many open sets `O_D`, which is a neighbourhood of
   `y`.
3. `hasLocalDomainEtaleFactorizations_inf_domainPreimage_of_t2Space`. This is
   the local step of `QuasiEtaleCompReduction` with a Hausdorff envelope
   `W` for the factorization of `f` on `D`. Its only premise is
   `EtaleDomainQuasiEtaleStatement`. The proof is that of
   `hasLocalDomainEtaleFactorizations_inf_domainPreimage`, with one change:
   - `P = w⁻¹(E)` is a domain of `W`, so its underlying space is Hausdorff
     (`T2Space.of_injective_continuous` for the inclusion `domainι W P`).
   - The morphism from `domainObj W P` to the envelope of `g` is quasi-étale
     by `EtaleDomainQuasiEtaleStatement`. Because its source is Hausdorff,
     `hasLocalDomainEtaleFactorizations_of_quasiEtale` gives its local
     factorizations.

## The theorem

`quasiEtale_comp_of_t2Space`. It suffices to show that `f ≫ g` has local
domain–étale factorizations (`HasLocalDomainEtaleFactorizations.quasiEtale`),
and `HasLocalDomainEtaleFactorizations.of_domain_cover` reduces this to a
cover. At a point `y` of `A`:

- `A` is Hausdorff, so `hasLocalDomainEtaleFactorizations_of_quasiEtale`
  applies to `f`. Lemma 2 then gives a finite family `C_D` of domains through
  `y` whose factorizations have Hausdorff envelopes.
- `B` is Hausdorff, so `hasLocalDomainEtaleFactorizations_of_quasiEtale`
  gives a finite family `C_E` for `g` at `f(y)`.

The cover is the finite family of the domains `D ⊓ f⁻¹(E)` for `D ∈ C_D` and
`E ∈ C_E`. Its union is a neighbourhood of `y` because `f` is continuous. On
each member, lemma 3 applies.

`quasiEtaleHausdorffCompReduction` introduces the premise, the morphisms,
the two Hausdorff hypotheses and the quasi-étaleness hypotheses of
`QuasiEtaleHausdorffCompReductionStatement`, makes the Hausdorff hypotheses
available as instances, and applies `quasiEtale_comp_of_t2Space`.

## Relation to the source

Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994),
registered as `berkovich-1994-vanishing-cycles-formal-schemes`, Lemma 3.1(i)
(printed p.544, PDF p.6), says that quasi-étale morphisms are preserved under
compositions. Its proof is one sentence: the statement follows from the
properties of étale morphisms and Theorem 3.4.1 of Berkovich,
*Étale cohomology for non-Archimedean analytic spaces*, Publ. Math. IHÉS 78
(1993), registered as `berkovich-1993-etale-cohomology`. This module proves
the composition clause for Hausdorff `A` and `B` from one named premise,
`EtaleDomainQuasiEtaleStatement`. The Markdown of `QuasiEtaleCompPrerequisites`
explains how that premise comes from Theorem 3.4.1 through Corollary 3.4.2
(printed p.67, PDF p.64) of the 1993 paper. The Hausdorff hypotheses on `A`
and `B` are not in the source. They make the domains of Berkovich's definition
of quasi-étale morphisms (printed p.543) closed, so that the domains missing a
point can be dropped. Local Hausdorffness, used for the envelopes, is part of
Berkovich's definition of analytic spaces (1993, §1.1 and Definition 1.2.3,
printed pp.13 and 16).
