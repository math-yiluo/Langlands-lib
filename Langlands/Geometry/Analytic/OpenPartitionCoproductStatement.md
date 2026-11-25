# Statement: an analytic space partitioned into open domains is their disjoint union

This module states, without proof, that an analytic space whose underlying
space is partitioned into open subsets is the coproduct of the corresponding
open domains in the localized category of analytic spaces. It contains one
Prop-valued definition,
`Langlands.Analytic.SaturatedAtlasPresentation.OpenPartitionCoproductStatement`.

## The statement

`OpenPartitionCoproductStatement : Prop` (universes `u v z`). Let `K : Type u`
be a complete ultrametric normed field, `J : Type z` an index type and
`Y : LocalizedCategory.{u, max z v, max z v}` an analytic space. Let
`U : J → Set (presentationOf Y).presentation.space` be a family of open
subsets of the underlying space of `Y` (`hU j : IsOpen (U j)`) that are
pairwise disjoint and cover the space. Then the cofan

`Cofan.mk Y (fun j => domainι Y ((presentationOf Y).openDomain (U j) (hU j)))`

is a colimit cocone, that is, a coproduct. Here
`(presentationOf Y).openDomain (U j) (hU j)` is the open subset `U j` as an
analytic domain of `Y`, `domainObj Y D` is the domain as an object of the
localized category, and `domainι Y D : domainObj Y D ⟶ Y` is its canonical
morphism (module `InvariantAnalyticDomains`). The conclusion is
`Nonempty (IsColimit …)` because the statement is a `Prop`.

In words: a morphism out of `Y` is the same as a family of morphisms out of
the pieces `U j`. The universes match the Library's chosen disjoint unions
(module `LocalizedDisjointUnion`), whose index type `J : Type z` is absorbed by
the universe `max z v` of the presentation data.

## Original source and provenance

Provenance: derived. The statement is the case of pairwise disjoint open
pieces of the gluing of morphisms over a quasinet in Berkovich, *Étale
cohomology for non-Archimedean analytic spaces*, Publ. Math. IHÉS 78 (1993),
registered as `berkovich-1993-etale-cohomology`: Definition 1.3.1 (printed
p.23, analytic domains, open subsets are analytic domains, and morphisms into a
domain factor uniquely through it) and Proposition 1.3.2 (printed p.24: for a
quasinet `{Y_i}` covering `X`, the sequence
`Hom(X, X') → ∏ Hom(Y_i, X') ⇉ ∏ Hom(Y_i ∩ Y_j, X')` is exact). The open
subsets `U j` cover `Y`, and each point lies in some `U j`, which is open and
therefore a neighbourhood of the point; so `{U j}` is a quasinet. For distinct
indices `U i ∩ U j` is empty, so every family of morphisms out of the pieces
agrees on the overlaps. Exactness of Berkovich's sequence then gives, for every
family of morphisms `U j → X'`, a unique morphism `Y → X'` restricting to it:
this is the coproduct property stated here with the Library's canonical
morphisms `domainι` of the open domains. The formulation (open analytic
domains, colimit cofans in `LocalizedCategory`) is chosen to match the
Library's API.

Motivation for the application: Berkovich, *Étale equivariant sheaves on
p-adic analytic spaces* (unfinished manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.1.2, printed p.2, constructs the induced space `X′ = X_{G/H}` of an
`H`-space `X` as the disjoint union `∐_{i∈G/H} X_i` of copies `X_i` of `X`;
Example 1.2.1(i), printed p.3, asserts that induction `U(H) ↦ U_{G/H}(G)`
gives isomorphisms of sites. The decomposition of a quasi-étale `G`-space `V`
over `X_{G/H}` into the inverse images of the copies `X_i`, to which this
statement is applied, is not in the manuscript: it is derived for the
Library's proof of Example 1.2.1(i), along the proof route sketched in
`InducedSiteEquivalenceStatement.md`.

## Role

This statement is a prerequisite for the proof of Berkovich's Example
1.2.1(i) (`QuasiEtaleSiteEquivalenceStatement`). The proof of
fullness and of essential surjectivity of the induction functor decomposes a
`G`-space over `X_{G/H}` into its parts over the copies of `X`. The universal
property of the coproduct gives the morphisms out of it.

## Scope

This is a statement module: nothing is proved here.
