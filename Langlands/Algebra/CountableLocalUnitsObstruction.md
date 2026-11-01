# Countable local units and the regular-module obstruction

Derived internal proof machinery authored by Worker 6 and checked for this
submission by Worker 345, motivated by Renard I.5.3,
printed p.27 / PDF p.33 in the French version dated 9 July 2026. The
registered original `renard-2026-representations-groupes-reductifs-padiques`
has SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source warns that the regular module need not be projective but does
not give this example or argument. All content here is a derived proof route.

For an arbitrary nonunital ring with a common right local unit for every
sequence of elements, `finite_image_support` says that an original
intertwiner from its regular left module to any actual direct sum has
only finitely many coordinates that are nonzero anywhere in its image.
Otherwise embed the natural numbers in the set of used coordinates and
choose one original vector witnessing each coordinate. A common right
local unit `e` for those vectors gives `f(a_n) = a_n • f(e)`. Each selected
coordinate must therefore be in the finite support of `f(e)`, contradicting
the injective sequence of selected coordinates. No unital action is imposed;
the domain action is original multiplication and the target is the published
coordinatewise original direct-sum action. The ring, index and target
carrier universes are independent.

`right_identity_of_regular_projective` uses the actual free orbit-map cover
of the lifted regular object, indexed by all its original vectors. This map
is surjective because a fixing idempotent for each target vector gives a
preimage in that vector's summand. If the regular object is projective, this
epimorphism has a section. Applying `finite_image_support` to the section
after inserting the universe lift gives finitely many used summand labels.
Choose a common two-sided idempotent local unit for their underlying ring
elements, using `IsIdempotented`. The orbit-sum image of every section vector
is fixed by right multiplication by this idempotent: expand the finite sum
and use associativity on each original term. Since the section followed by
the cover is the identity, this idempotent is a right identity on every
original ring element. `regular_not_projective` is the contrapositive.

The ring need not be commutative. No claim about the projectivity of the
free cover is used. Its carrier is the actual published finite-support sum
of lifted regular carriers, with original actions. The lift universe is
independent of the ring universe. The concrete countable-support algebra
specialization is implemented in the accompanying
`NonUnitalModuleFreeCounterexampleProof` entry module.


`regularSingleIso` is the categorical isomorphism from the original lifted
regular module to a one-element-indexed actual direct sum. Its forward map
is the published singleton inclusion; its inverse is evaluation at that
single coordinate. Both preserve the original action. Their composites are
identities by the singleton evaluation and by equality of all coordinates.
Choosing the one-element type in the displayed carrier universe proves
`regular_isFree` in the published exact definition.
