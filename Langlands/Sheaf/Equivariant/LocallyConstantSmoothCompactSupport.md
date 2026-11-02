# Compact functions and compact sections of the full smooth locally constant sheaf

This internal ordinary-open comparison connects the full compactly supported
locally constant function representation to the existing compact-section functor
on smooth equivariant sheaves. The space, commutative ring and module carriers
share universe `u`, required by the existing stalk and smooth-sheaf APIs; the
group universe `v` is independent. Individual spatial operators are continuous.

`stalkEquiv` composes the actual equivariant linear equivalence between all
compact functions and all local-vanishing compact sheaf sections with the proved
identity-on-sections equivalence to all stalk-supported compact sections.
`algebraicStalkComparison` is the composition of the two original natural
isomorphisms, so it retains every coefficient intertwiner.

For the smooth constructions, the group has a topology and the action satisfies
`HasStableNeighbourhoods`. The coefficient representation is smooth. First form
the previously constructed full smooth locally constant sheaf, and apply the
published `smoothSheafCompactSections` functor. That functor proves smoothness
of every compact section of every smooth sheaf. Transfer it through the inverse
of `stalkEquiv`: this proves smoothness of every compact function under these
hypotheses, without requiring joint spatial continuity or restricting to smooth
vectors.

`functionFunctorOfStableNeighbourhoods` retains the full compact-function
representations and original pointwise coefficient maps. `smoothSheafComparison`
identifies this functor with `smoothSheafSectionsFunctor`, the actual composite
of the full smooth sheaf construction and the published compact-section functor.
Its naturality is the pointwise coefficient-map equality. Forgetting smoothness
recovers exactly `algebraicStalkComparison`, as proved by
`smoothSheafComparison_toRep`.

The provenance is internal composition and smoothness transfer from the imported
actual function, sheaf, support and smooth-sheaf constructions. No new
original-literature assertion is made. This neither identifies analytic or etale
sites nor proves Godement acyclicity, a derived comparison, an arithmetic-tower
result or the Harris specialization.
