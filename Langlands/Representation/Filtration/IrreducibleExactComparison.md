# Exact injections and simple composition-factor comparisons

These internal algebraic helpers support the local induction reduction for
the repeated cuspidal triple transfers. They assert no local product
irreducibility or Jacquet transfer.

`liftThroughInjection` restricts an intertwiner to the range of a supplied
injective intertwiner, then applies the inverse of that intertwiner's
linear equivalence onto its range. Injectivity proves equivariance.
`injection_liftThroughInjection` records its actual factorization.

`equiv_left_or_injective_right` considers a nonzero map from a simple
representation into an exact sequence's middle term with simple left term.
If its composite to the right term is zero, the map lifts through the
injection and is a nonzero map between simple representations, hence an
actual equivalence. Otherwise simplicity of the source makes the composite
injective. Surjectivity of the sequence's right map is unnecessary.

`oneSlotGradedEquiv` identifies the actual sole quotient of a one-slot
zero-to-whole filtration with the original representation.
`nonempty_equiv_of_sameFactors` uses composition length one to show that
matching multiplicity-sensitive Jordan–Hölder factors with a simple
representation gives an actual equivalence. All coefficient, monoid and
carrier universes are independent. The provenance is the existing actual
filtration definitions and elementary linear and simple-module arguments.
