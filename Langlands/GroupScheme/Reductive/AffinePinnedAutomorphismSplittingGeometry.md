# Geometric splitting from local pinned representatives

This internal reduction supplies the two geometric inputs of the affine
automorphism-group assembly from the separate existence predicate
`HasFppfLocalPinnedRepresentatives`.

For an automorphism over the connected original affine base, choose a global
fppf-locally pinned representative of its inner class using the relative
comparison descent theorem. Preservation of the canonical cocharacter
identifies the canonical dynamic parabolic functors and hence their supplied
Borel representatives. Connected coordinate alignment gives one based full
root-datum equivalence for the actual torus map. The fppf-local extraction
bridge then gives the exact original pinned-automorphism predicate with one
label, including its actual global chosen-vector equations.

The canonical identity-pullback comparison transports the chosen normalized
automorphism back to the original model and reflects inner equivalence. The
discrepancy in the required action order has a unique actual global section of
every supplied full-centre fppf quotient, so the original automorphism is the
product of that adjoint action and the exact pinned automorphism.

For separation, an exact pinned automorphism in the adjoint action image is
fppf-locally inner and becomes fppf-locally pinned on its actual identity
pullback. Relative pinned inner rigidity makes that pullback the identity.
Faithfulness of identity base change reflects the equality to the original
automorphism, and label uniqueness gives the identity label.

The construction `automorphismProjectionOfLocalPinnedRepresentatives` gives
the actual group homomorphism from ambient automorphisms to root-datum
automorphisms from these geometric inputs and pinned full faithfulness. Its
proved kernel formula is exactly the image of the supplied adjoint action.

The final theorem combines this geometry with pinned full faithfulness to
prove the unchanged affine automorphism-group proposition conditionally on
the two explicitly supplied propositions. It does not prove either pinned
full faithfulness or local pinned-representative existence.
