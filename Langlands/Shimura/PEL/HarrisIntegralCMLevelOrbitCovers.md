# Finite-etale covers of actual Harris monodromy orbits

This internal construction retains the actual integral-action family and the
nonempty raw-level premise from `HarrisIntegralCMLevelContinuousOrbits`.
It additionally requires a connected locally noetherian test scheme and an
algebraically closed geometric point field, exactly as the published geometric
continuous-action equivalence does.

The selected cover is an object preimage of the actual finite continuous orbit
action under `continuousActionFunctor s hs`. The equivalence premise is proved
by `geometricContinuousActionEquivalence s hs`, not supplied as new data.
The corresponding object-preimage isomorphism identifies the actual geometric
fibre action with that orbit action. Forgetting the finite continuous action
packaging gives a bijection from actual geometric lifts into the cover to the
actual raw monodromy orbit; the action isomorphism's commuting square gives its
equivariance for the same fundamental group. Applying the inverse fibre
equivalence to the distinguished raw class gives an actual geometric lift
into the cover, and the final theorem verifies its image is that class.

The provenance is internal, by specialization of the published finite-etale
equivalence to the previously constructed actual orbit action. The result
constructs a finite-etale cover and its actual equivariant fibre comparison.
It does not assert finiteness or representability of the whole raw level set,
representability on the full componentwise admissible category, or completion
of the normalized Harris division-case representability target.
