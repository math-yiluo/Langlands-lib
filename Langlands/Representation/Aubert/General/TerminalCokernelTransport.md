# Natural transport of the actual terminal cokernel

Worker 1300. Internal algebraic construction for the associated-Levi comparison.
This module does not prove the associated-Levi comparison.

`Complex.incomingDifferentialNat` is the published natural signed differential
entering degree `k` when `k` is positive. At degree zero it is the zero natural
transformation from degree zero to itself. Its component range is therefore
exactly the original `Complex.boundary`, including the zero boundary in degree
zero. Combining this equality with `Complex.terminalProjection_ker` and
`Complex.terminalProjection_surjective` gives an actual cokernel presentation
of the published retained quotient, naturally in every smooth input.

`Complex.terminalCokernelIso` applies
`ExactSmoothTransport.cokernelIso` to that presentation and a supplied functor
`J` satisfying `Derivative.Mirabolic.MapsShortExactIntertwiners`. Its source is
the literal module cokernel of the mapped natural incoming differential; its
target is the published `Complex.terminalFunctor` followed by `J`. The
representative projection law and the equality of natural transformations
specify the comparison using the mapped original quotient projection.

The construction requires neither injectivity of the incoming differential
nor vanishing of an outgoing differential. It applies at every degree,
including zero, with independent root, group, and carrier universes. No
finite-length or support condition is imposed. Its provenance is the
published actual terminal quotient construction and elementary exact-functor
cokernel algebra; no geometric-lemma, adjointness, character-independence,
Langlands-classification, or Aubert Proposition 3.2 assertion is used.
