# Equivariant sheaves on an actual topological action

Author: Worker 13.

For a group `G` acting on `X`, an object of `TopologicalSheaf G X A` is an
`A`-valued presheaf on the accompanying `ActionOpens` category whose restriction
to ordinary open inclusions satisfies Mathlib's sheaf condition.
`underlyingPresheaf` is the actual precomposition functor. `sheafProperty`
tests its ordinary sheaf condition, and `TopologicalSheaf` is the corresponding
full subcategory of the functor category.

Morphisms are natural transformations on all group-labelled arrows. They
therefore commute with both restriction and transport of sections. The
category laws come from Mathlib's functor and full-subcategory constructions.
`toTransportPresheaf` is fully faithful. `toSheaf` constructs the ordinary
sheaf and is faithful: its components at every open recover every component
of the original natural transformation. For preadditive coefficients, the
equivariant sheaf category is preadditive by the existing pointwise and
full-subcategory instances.

`sections` gives an actual functor to `Action A G`. The operator at `g` is the
presheaf map associated with the inverse-label arrow `g⁻¹` on the whole space.
The reversal of arrows and the inverse label together give the left-action
law. `invariantSections` gives the corresponding action of a subgroup on any
open subset stable under that subgroup. Its stability premise is a property
of the given point action. `restriction` constructs the natural equivariant
restriction maps between stable opens; the commutation equations are proved
by equality of labelled arrows and presheaf functoriality.

When the individual group operators are continuous, `translateSections`
constructs an isomorphism from sections on `U` to sections on `gU`. Its
naturality in the sheaf is proved. These are maps between sections over
different open sets of the actual space.

This is derived topological infrastructure for the transport-of-sections
description in Berkovich's supplied unfinished *Etale equivariant sheaves on
p-adic analytic spaces*, section 1.4, printed p.7, before Definition 1.4.1.
Worker 13 read that original passage. It describes compatible isomorphisms
between sections on translated site objects and the induced action on
subgroup-stable objects. Here those objects are ordinary opens; the analytic
étale or quasi-étale site and its distinguished or compact objects remain
the analytic branch's constructions. Smoothness and continuity of section
actions are additional conditions, not consequences of algebraic equivariance.
No identification with Harris's smooth étale sheaf category is asserted.

Source registration:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The universes of `G`, `X`, objects of `A`, and morphisms of `A` are independent.
There is no topology on `A`. Individual continuity is required only for
translations of opens. Dependencies are the companion `ActionOpens` module
and Mathlib's ordinary sheaves, full subcategories, actions and preadditive
functor categories at commit `5ed2965256430c3649e86755f9576b54eca72435`,
Lean 4.34.0. All displayed action and functor laws are proved.
