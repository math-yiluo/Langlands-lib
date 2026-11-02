# The actual Picard arrow relation as a smooth quotient input

This internal adapter connects the previously constructed actual Picard
arrow and endpoint-kernel schemes with the general smooth-relation
interface. It constructs input data for the first quotient and proves
their required properties. It does not apply or assume the geometric
quotient theorem.

`atlasArrowScheme_locallyOfFiniteType` writes the structure map of an
arrow scheme as its smooth endpoint followed by the locally finite type
structure map of the object atlas. Smooth morphisms are locally of finite
type, and composition preserves that property.

`representedKernel_isEquivalenceRelation` applies the proved full
presheaf kernel-pair lemma to the generic relation predicate. The scheme
representing the kernel is included as its actual fppf algebraic space.
Its section types and projection maps are the same full lifted Yoneda
types and maps used by the kernel-pair lemma.

`schemeRelation_hasSmoothProjections` uses the identity of this scheme as
its common etale atlas. Each base change of the identity is represented
by the test scheme with its identity projection; hence it is etale and
surjective in the full relative-morphism sense. The two atlas composites
are exactly the supplied actual smooth scheme projections.

`exists_smoothArrowRelation` combines these adapters with the actual
arrow-scheme and smooth endpoint-kernel constructions. It retains the
isomorphisms representing all arrows and their full kernel, the exact
endpoint equalities, both original smooth surjective endpoint maps,
both smooth kernel projections, the full presheaf kernel pair, and the
locally finite type conclusion for the arrow scheme. It also supplies
the generic equivalence-relation and smooth-projection predicates.
Every scheme test and every actual arrow section remains present,
uniformly at universe `u`. The two geometric quotients and identification
with the actual ordinary etale Picard class sheaf remain open.

`arrowKernelQuotientSheaf` fixes the etale sheafification of the pointwise
classes for this represented endpoint-kernel relation.
`arrowKernelQuotientMap` is the canonical arrow-class map followed by
the sheafification unit. These definitions use the generic quotient
constructions with the proved actual relation witness. They supply
neither fppf descent nor representability of this sheaf; those geometric
properties still require the independently proved quotient theorem.
