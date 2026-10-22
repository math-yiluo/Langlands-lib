# Group transport between open subsets

Author: Worker 13.

Let a group `G` act on a topological space `X`. The objects of `ActionOpens G X`
are the actual open subsets of `X`. A morphism from `U` to `V` is a group
element `g` with `g • U ⊆ V`. Distinct group elements remain distinct morphisms,
even when they induce the same point map. Thus this construction retains
isotropy for a nonfaithful action.

Identity morphisms have label `1`. Composition of a label `g` followed by a
label `h` has label `h * g`. The category laws are proved using the action and
group laws; the containment certificates are proved from the two input
containments. `inclusion` sends an ordinary open inclusion to a label-one
morphism and proves both functor laws. `inclusionHom` gives the same
label-one restriction arrow between already bundled transport objects.

If each group element acts continuously, `translate g U` is the actual
translate, written as the preimage of `U` under multiplication by `g⁻¹`.
`translationIso` has label `g` with inverse label `g⁻¹`. Its inverse equations
and compatibility with inclusions are proved.

For contravariant sections, `sectionArrow g` over the whole space has label
`g⁻¹`. On an open stable under an actual subgroup `H`, `invariantArrow` uses
the same inverse-label convention. The identity and multiplication equations
are proved. They give left actions on sections in the companion module.
The hypothesis about the stable open is a pointwise property of the given
group action; it does not supply section maps as arbitrary data.

This is derived infrastructure for moving-space equivariance, motivated by
Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, the supplied
unfinished 1995–1996 manuscript, section 1.4, printed p.7, before
Definition 1.4.1. That passage describes compatible transport of sections
between translated objects and the induced action on a stable object.
Here the site objects are ordinary open subsets of a topological space.
The analytic étale and quasi-étale sites, their compact or distinguished
objects, and the lifting of open subgroups to such objects remain separate
constructions. This module does not identify ordinary open-set sheaves with
étale sheaves.

The original cited passage was read by Worker 13. Source registration:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The space and group universes are independent. The category itself needs no
topology on `G` and no continuity hypothesis; translation of open objects
requires `ContinuousConstSMul G X`. Formal dependencies are Mathlib's group
actions, categories and open subsets in the pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0. No project axiom or
comparison theorem is assumed.
