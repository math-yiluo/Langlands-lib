# Points of identity jets and their centralizers

This module defines two predicates on points of a group scheme `G` over an
arbitrary scheme `S`. They use the Library's identity jets:
`IdentityJet.scheme G n` is the closed subscheme of `G` cut out by the
`(n + 1)`-st power of the ideal of the unit section, and
`IdentityJet.inclusion G n` is its closed immersion into `G`. For a separated
group this is the `n`-th infinitesimal neighbourhood `G_n` of the unit
section in the sense of SGA 3, Exposé XI, 6.10.

- `IdentityJet.IsJetPoint G n x` says that the point `x : V ⟶ G.X` on a test
  scheme `V : Over S` lies in the order-`n` jet. Its underlying scheme
  morphism `x.left` must factor through `IdentityJet.inclusion G n`. Since
  the inclusion is a monomorphism, the factorization is unique when it
  exists.
- `IdentityJet.CentralizesJet G n g` says that the point `g : U ⟶ G.X`
  centralizes the order-`n` jet. For every refinement `a : V ⟶ U` and every
  jet point `x : V ⟶ G.X`, the point `a ≫ g` commutes with `x` in the group
  of points of `G` on `V`.

The second predicate is membership in the centralizer functor
`Centr_G(G_n)` of SGA 3, Exposé XI, Corollary 6.11. Every refinement of the
test scheme is tested, so the predicate is preserved by restriction along
any morphism of test schemes. These are internal definitions with no new
mathematical content. They state the intermediate results
`JetCentralizerStabilizationStatement` and
`JetConjugationRepresentationStatement`.
