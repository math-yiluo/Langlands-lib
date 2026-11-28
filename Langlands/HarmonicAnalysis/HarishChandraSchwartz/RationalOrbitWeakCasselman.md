# The Casselman pairing for weak orbit coefficients

This module specializes the weak tensor formula `standardWeakTensorCasselman` to the
coefficients of smooth sections of a discrete-series orbit. In Waldspurger's proof of
Proposition V.1.1, the weak constant term of the induced coefficient is the coefficient
given by the normalized pairing of the two weak Jacquet classes. The use of the pairing
is justified by the constant-term formula in the proof of III.5.1.

`rationalInducedCoefficientTensorEquiv` uses `CompactInduction.coefficientTensorEquiv` for
the actual standard parabolic and the Haar probability of the inducing compact subgroup.
It identifies the product induction with the tensor product of normalized induction and
its smooth dual. `rationalOrbitCoefficientTensor` applies that equivalence to the section
at the specified unitary twist. The representative formula
`rationalInducedOrbitCoefficientMap_representative` then identifies the coefficient of this
tensor with the orbit coefficient at the class of the twist.

`RationalOrbitWeakCasselmanStatement` takes a compact-open normal basis satisfying the
standard parabolic basis conditions for the specified split component of the lower Levi.
The supplied square-integrability data index the inducing orbit and its coefficient map.
For any stable Casselman pairing and unitary twist, the weak constant term of the
section's coefficient is the pairing coefficient of the two projected normalized
Jacquet classes, extended linearly to the section's tensor.
`rationalOrbitWeakCasselman` obtains admissibility of normalized induction from
`CompactInduction.induced_isAdmissible`, applies `standardWeakTensorCasselman`, and substitutes
the tensor's coefficient for the original orbit coefficient.

Source. J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, III.5.1 (printed pp. 269–270)
and the proof of V.1.1 (printed pp. 289–290). The registered source is
`waldspurger-2003-plancherel`.
