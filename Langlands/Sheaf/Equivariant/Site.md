# The transport site of a group action on a topological space

Author: Worker 61. Builds on Worker 13's published transport category
`ActionOpens G X` and equivariant sheaf category `TopologicalSheaf G X A`.

Let a group `G` act on a topological space `X` by continuous individual
operators. An arrow `V ⟶ U` of the transport category is a label `g` with
`g • V ⊆ U`; label-one arrows are the ordinary inclusions.

`transportTopology G X` is a Grothendieck topology on the transport category.
A sieve `S` on `U` covers `U` when its label-one inclusions cover `U` in the
ordinary sense, that is, when `inclusionSieve S` belongs to Mathlib's topology
of open covers. `mem_transportTopology_iff` states this explicitly with
`inclusionHom`. `mem_transportTopology_iff_exists_smul` gives the equivalent
condition that every point of `U` is `g • v` for some arrow `V ⟶ U` of `S` with
label `g` and some `v ∈ V`. The topology axioms are proved. Pullback stability
uses the continuity of each operator: a cover is pulled back along an arrow of
label `g` by intersecting with the preimage under `g`.

These proofs rely on factoring arrows. `ActionOpens.translate_le` shows that
the translate `g • V` lies in `U`.
`ActionOpens.exists_translationIso_comp_inclusionHom`
writes every arrow as the published translation isomorphism `V ≅ g • V`
followed by a label-one inclusion. `ActionOpens.translationIso_inv_comp` gives that
inclusion as the inverse translation followed by the arrow, so every sieve
containing the arrow contains the inclusion. `sieve_arrows_of_eq` is a small
helper for sieve membership along equal arrows.

`inclusion_coverPreserving` and `inclusion_compatiblePreserving` show that the
label-one inclusion functor `Opens X ⥤ ActionOpens G X` preserves covers and
compatible families. Compatibility uses the factorization: two arrows with the
same label factor through the same translate. Mathlib then makes the functor
continuous (`inclusion_isContinuous`), so restricting a transport sheaf to
label-one inclusions gives an ordinary sheaf. Conversely,
`isSheaf_of_isSheaf_inclusion` proves that the ordinary sheaf condition implies
the transport sheaf condition for type-valued presheaves. One first glues the
label-one part of a compatible family; the factorization and compatibility then
identify the restriction to every labelled arrow. Uniqueness follows from the
ordinary sheaf condition.

For an arbitrary coefficient category `A`, `isSheaf_transportTopology_iff`
states that a presheaf on the transport category is a sheaf for
`transportTopology G X` exactly when it satisfies the published `sheafProperty`.
The converse direction is applied to each `A`-valued sheaf condition through
Mathlib's coyoneda formulation. `sheafEquivalence` is the resulting equivalence
`TopologicalSheaf G X A ≌ Sheaf (transportTopology G X) A`. Both categories are
full subcategories of the same presheaf category, and the equivalence is the
identity on underlying presheaves and natural transformations. The two `simp`
lemmas record this on objects.

Universes are those of the published modules: `G : Type uG`, `X : Type uX`, and
an arbitrary coefficient category. The group needs no topology. The sheaf
conditions involve no smoothness.

Provenance: this is derived infrastructure. Berkovich, *Etale equivariant
sheaves on p-adic analytic spaces* (unfinished 1995–1996 manuscript), section
1.4, printed page 7, defines a sheaf with a discrete group action by functorial
transport bijections `F(U) → F(gU)`. Theorem 1.4.2, printed pages 8–10,
identifies equivariant sheaves with sheaves on a site `X(G)` attached to the
`G`-space. The present transport site plays the analogous role for ordinary
open sets. It is a different site from Berkovich's analytic étale site, and the
equivalence is proved directly here. Neither Theorem 1.4.2 nor the
analytic étale specialization is formalized. Worker 61 read sections 1.4–1.5,
printed pages 7–12, of the registered original
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member PDF SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`).

Dependencies: the published `Langlands.Sheaf.Equivariant.Topological`, and
Mathlib `Sites.Spaces`, `Sites.CoverPreserving` and `Sites.Continuous`, pinned
to Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
