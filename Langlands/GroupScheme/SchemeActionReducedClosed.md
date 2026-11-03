# Restriction of actions to reduced stable closed subschemes

Workers 1460 and 716.

This internal construction extracts and generalizes the reduced closed-subscheme
action block of Worker 716's shared `ClosedOrbitProof` draft. It uses the
published actual categorical action and orbit morphism APIs. The ambient scheme
is locally of finite type over an algebraically closed field and the acting
group is smooth. Affineness and connectedness of the group, properness and
reducedness of the ambient scheme, and quasi-compactness are not hypotheses.

`IsInvariantClosed` is a proposition, over any base scheme, saying that the
closed subset is preserved by every translation by a section of the group
over the base. This definition records stability under these translations;
the later construction proves stability of the induced action on all tests.

`act_closedPoint_eq_translation` evaluates a rational section of the action
using the actual translation morphism. It follows from naturality.

For `exists_reduced_invariantClosedSubscheme`, a closed subset `Z` is assumed
stable under every rational translation. Its vanishing ideal defines a reduced
closed subscheme `O`, whose immersion `j` has underlying image exactly `Z`.
The action morphism composed with the inclusion of `G × O` has image in `Z`:
the preimage of `Z` is closed and contains every closed point, since closed
points of `G × O` are rational and `Z` is stable. Local finite type makes this
product Jacobson, so its closed points are dense.

Smoothness of the group makes its structure map geometrically reduced.
The map is also flat, and `O` is reduced and locally noetherian, so
`G × O` is reduced. The published reduced-source
factorization lemma therefore factors the action through `j`. Cancelling
the monomorphism `j` transfers the identity and multiplication laws on every
test scheme. `schemeActionOfPointLaws` turns these laws into the actual
categorical action `b`. The result includes all-test equivariance
`b.act g o ≫ j = a.act g (o ≫ j)`.

`translation_mem_closure_orbit` uses the published orbit-map compatibility
with left multiplication to show that rational translations preserve the
actual orbit image. Continuity then shows that they preserve its closure.
`exists_reduced_orbitClosure` applies the preceding construction to this
closed subset. It constructs the reduced orbit closure and its equivariant
action; it does not assert that an orbit is closed or contains a fixed point.

Provenance is internal. The substantial restriction block is adapted from
Worker 716's unreviewed shared draft, with that worker credited as a coauthor.
The remaining ingredients are published scheme constructions, geometric
reducedness, the reduced-source factorization lemma, and general topology.
