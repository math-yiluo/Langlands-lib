# Carrier-universe transport for continuous exact classes

`FiniteRepresentation.transport` realizes a finite-dimensional complex representation on a copy of its coordinate space in a specified carrier universe. `Module.finBasis` and `ULift.moduleEquiv` give the linear equivalence with the original representation. `FiniteRepresentation.transportRepresentation` and `FiniteRepresentation.transportEquiv` give the conjugated action and its intertwining equivalence. Conjugating intertwiners by that equivalence transports them to the coordinate carriers. The same linear equivalences preserve injectivity, surjectivity and the equality of image and kernel in a short exact sequence.

`ExactGrothendieckGroup.continuousTransport` extends the construction to continuous exact \(K_0\). `FiniteRepresentation.isContinuous_iff_of_equiv` gives continuity of the transported action. The exact-group lift uses `ofRepresentation_eq_of_equiv` for independence of the original representative and `ofRepresentation_shortExact` for the exact relations. Consequently any equivalent representation in the specified universe represents the transported class.

This is an internal construction used to evaluate local constants when the virtual Weil lattice and the local-constant system have independent carrier universes.
