# Induction of sheaves to equivariant sheaves

Author: Worker 13. Built on the published transport category
`Langlands.Sheaf.Equivariant.ActionOpens`, Worker 61's transport site and
sheaf equivalence `Langlands.Sheaf.Equivariant.Site`, and the abelian
structure in `Langlands.Sheaf.Equivariant.Abelian`.

Let `R` be a commutative ring and let a group `G` act on a topological space
`X` by continuous translations, all in one universe `u`. `toSheaf G X A`
forgets the group-labelled arrows of an equivariant sheaf. This module
constructs a left adjoint of `toSheaf G X (ModuleCat R)` that preserves finite
limits. Consequently `toSheaf` sends injective equivariant module sheaves to
injective ordinary sheaves.

## Translates are final

For an open `U`, regarded as an object of the transport category, the left
Kan extension along the inclusion `ActionOpens.inclusion G X` of ordinary
opens is computed over the category of costructured arrows
`CostructuredArrow (inclusion G X).op (op U)`. An object of this category is
an ordinary open `V` with a labelled arrow `U ⟶ V`, that is, an element `g`
with `g • U ⊆ V`. `ActionOpens.translateArrows U` is the functor from the
discrete category on `G` sending `g` to the translate `g • U`
(`ActionOpens.translate g U`) with its translation arrow.

Ordinary inclusions have label one, so a factorization of a labelled arrow
through a translate `g • U` forces `g` to be the label of that arrow
(`ActionOpens.label_eq_of_hom`). The arrow does factor through the translate
by its own label (`ActionOpens.toTranslate`). Morphisms between ordinary opens
are unique. So for every object `d`, the category of factorizations of `d`
through translates is nonempty and connected. Hence `translateArrows U` is
final (`ActionOpens.translateArrows_final`). Mathematically, the colimit over
the costructured arrows is the direct sum of the values on the translates
`g • U`. The module uses only finality and does not construct this
isomorphism.

## Exactness of the left adjoint

Coproducts of modules are exact (Mathlib's `AB4` instance for
`ModuleCat`). Mathlib's `hasExactColimitsOfShape_of_final` pushes this
exactness along the final functor `translateArrows`. This gives
`costructuredArrow_hasExactColimitsOfShape`: colimits indexed by these
costructured-arrow categories are exact. Mathlib's `lanEvaluationIsoColim`
identifies each value of the left Kan extension functor
`(ActionOpens.inclusion G X).op.lan` with such a colimit. So
`lan_preservesFiniteLimits` shows that left Kan extension of module
presheaves from ordinary opens to the transport category preserves finite
limits. Labels are preserved, so for a nontrivial group these
costructured-arrow categories are disconnected. Then the inclusion is not
representably flat and Mathlib's flatness criterion does not apply. The
finality argument replaces it.

`transportInduction` is Mathlib's explicit pullback of sheaves along the
continuous inclusion functor
(`Functor.sheafPullbackConstruction.sheafPullback`). It applies left Kan
extension to the underlying presheaf and then sheafifies for the transport
topology. It preserves finite limits (`transportInduction_preservesFiniteLimits`),
because forgetting the sheaf condition, left Kan extension and sheafification
each do. `induction` composes it with the inverse of the published
equivalence `sheafEquivalence` between transport sheaves and equivariant
sheaves. It also preserves finite limits (`induction_preservesFiniteLimits`).

## Adjunction and injectives

`pushforwardIso` identifies restriction of transport sheaves along the
inclusion, after the equivalence, with `toSheaf`, by identity components.
`inductionAdjunction` composes Mathlib's adjunction
`Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` with the
equivalence and this isomorphism. It proves `induction R G X ⊣ toSheaf G X
(ModuleCat R)`. A right adjoint whose left adjoint preserves monomorphisms
preserves injective objects (Mathlib's
`Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`).
This gives the instance `toSheaf_preservesInjectiveObjects`.

## Provenance and scope

This is internal infrastructure for comparing derived functors on
equivariant sheaves with ordinary sheaf cohomology. Berkovich, *Etale
equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), section 1.5, printed pp.11–12, defines `H^q_c(X(G), F)` and
`H^q_c(X{G}, F)` as derived functors of compactly supported (invariant)
sections. Corollary 1.5.2(i) identifies `H^q_c(X{G}, F)` with
`H^q_c(X, b^* F)`, the cohomology of the sheaf with its equivariance
forgotten. Berkovich proves this through the softness of the Godement
resolution (Proposition 1.5.1). Worker 13 read these passages in the
original. The present module takes a different route, which it does not
complete: an exact left adjoint of the forgetful functor, so that injectives
stay injective after forgetting equivariance. The module proves no comparison
of cohomology. It needs, in addition, exactness of `toSheaf` and the
identification of section functors.

The setting is the ordinary-topological transport site with an abstract
group, not Berkovich's analytic étale site or a topological group. No
smoothness or discreteness condition is used or claimed.

Source registration:
Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

All imported modules are present in Library commit
`354dfade2c499262492d6db74cb58fd887ffed5f`.
