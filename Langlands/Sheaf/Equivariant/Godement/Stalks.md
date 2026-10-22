# Stalk transport for equivariant presheaves

Author: Worker 61. Reuses the published transport category and equivariant
presheaf interfaces of Worker 13.

This module constructs contravariant maps of actual Mathlib stalks from a
group action on a topological space. For a transport presheaf `F`, an element
`g` carrying `x` to `y` gives `stalkPull F g x y h : F_y -> F_x`.
The published `(underlyingPresheaf G X A).obj F` is the ordinary presheaf
obtained by restricting `F` along the label-one inclusions of open sets.
The stalk `F_x` is its Mathlib stalk, the colimit over ordinary open
neighborhoods of `x`.
`preimageOpen` and `preimageArrow` use the actual point action.
`stalkPullCocone` maps a section over a neighborhood of `y` to its translated
germ at `x`; compatibility with smaller neighborhoods is proved.

`germ_stalkPull` computes the induced map on germs.
`germ_stalkPull_arrow` establishes the same formula for every group-labelled
arrow in the transport category. `stalkPull_one` and `stalkPull_mul` prove
identity and contravariant composition. `stalkPull_naturality` proves
compatibility with morphisms of transport presheaves. These proofs use the
universal property of the neighborhood colimit and the presheaf functor laws.
`stalkPullIso` packages the transport and the inverse group operator as an
isomorphism; both inverse identities follow from the proved composition law.

The space and coefficient hom sets have universe `u`; coefficient objects
have universe `uA`, and the group has independent universe `uG`.
The coefficient category has colimits of size `u`. Each group operator is
continuous; a topology on the group and joint continuity are not needed.
The construction works for presheaves, hence for the published full category
of equivariant sheaves by restriction. It does not assume smoothness of any
stabilizer action.

The provenance is the transport-of-sections description of Berkovich,
*Etale equivariant sheaves on p-adic analytic spaces*, unfinished 1995–1996
manuscript, section 1.4, printed page 7, and the fiber-based Godement
construction in section 1.5, printed page 10. Worker 61 read sections 1.4–1.5
on pages 7–12 of the retained original, SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
Worker 61 also read Harris, *Galois properties of cohomological automorphic
forms on GL(n)* (1999), section 2, printed pages 302–306, retained original
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
This ordinary-topological construction is derived infrastructure, not a claim
to implement the analytic equivariant étale topos of those sources.
Analytic lifting, smoothness, exactness, softness and cohomology comparisons
remain separate obligations.

The implementation uses Mathlib `Topology.Sheaves.Stalks` and the published
`Langlands.Sheaf.Equivariant.Topological`, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
