# Character detection from an epimorphic subgroup product

This internal construction works over an arbitrary base scheme `S` at universe
`u`. It isolates a formal reduction needed for central-torus character detection.
Its provenance is the direct argument below from actual group-scheme morphisms,
multiplication and categorical epimorphisms.

For group-scheme homomorphisms `i : Z ⟶ G` and `d : D ⟶ G`,
`subgroupProductMap i d` is the scheme morphism over `S` from the product of the
underlying `S`-schemes of `Z` and `D` to the underlying `S`-scheme of `G`.
It sends a pair of points to the product of their images, in that order.
Neither homomorphism is required to be a closed immersion, and centrality is
not required for this underlying scheme map to exist. The construction does not
assert that it is a homomorphism of product group schemes.

`comp_eq_one_of_epi_subgroupProductMap` assumes that this underlying scheme map
is an epimorphism in `Over S`. If a group-scheme homomorphism `f : G ⟶ H` to a
commutative target is trivial on both `i` and `d`, preservation of multiplication
shows that its precomposition with the product map is the identity-valued
morphism. Cancelling the epimorphism gives `f = 1`. This uses equality of scheme
morphisms, without an assertion about surjectivity on rational points.

`IsDerivedSubgroup.characterRestrict_ne_zero_of_epi_subgroupProductMap` assumes
that `d` actually exhibits the Library's derived subgroup and that the product
map is an epimorphism. The same-base annihilation lemma from
`Derived.KernelAnnihilation` makes every rational character trivial on `d`.
If a nonzero character were also zero on `i`, the preceding cancellation would
make the character zero. Thus its restriction along `i` is nonzero.

This unit does not construct a central torus or an actual derived subgroup,
and does not prove the epimorphism premise. In the reductive application those
remain structural proof obligations. It does not assert
`CentralTorusCharacterStatement` or `CentralSplitTorusCharacterStatement`.
No perfectness, characteristic, splitness or field hypothesis is imposed.

Authorship: Worker 1306.
