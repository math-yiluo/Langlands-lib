# Weight decomposition for actual automorphic split-torus actions

This module extends the published universal adjoint coefficient construction to
the differential of an arbitrary actual automorphic action. It is internal
infrastructure derived from existing coefficient extraction, reconstruction,
and action naturality; it assumes no semigroup realization theorem.

The differential of a constant acting point commutes with every group-algebra
coefficient. The proof reconstructs a Lie vector as a finite sum of monomials
times constant vectors, uses linearity and differential naturality on every
term, then extracts the selected coefficient.

The universal split-torus point gives `universalDifferential`.
Translated evaluation multiplies that universal point by a constant acting
point; the differential representation carries this to composition.
Consequently each finite universal coefficient has its own exponent weight.
Pure weights have singleton coefficients, and evaluation at the identity
shows that the coefficients sum to the original vector.

Over an arbitrary field k, `characterActionCoefficients` reindexes the
exponents by the actual character lattice of the standard split torus.
`characterActionCoefficients_mem` proves that each coefficient belongs to
the existing all-test-algebra differential weight space.
`characterActionCoefficients_of_mem_lieWeightSpace` proves the singleton
formula on each such weight space. Together with the sum formula these
give the internal direct-sum theorem `splitTorus.isInternal_lieWeightSpace`.

`AutomorphicAction.lieWeightSpace_comapIso` compares weight spaces after
changing the acting torus by an actual group-scheme isomorphism, pulling
back the actual character and preserving its value on every test algebra.
Finally `AutomorphicAction.isInternal_lieWeightSpace_of_isSplitTorus`
proves the internal direct-sum decomposition for any split torus T and any
homomorphism j from T into the acting group H of an actual automorphic
action of H on G. The target G is affine and locally of finite type over k.
There is no smoothness, connectedness, reductivity, or conjugation
assumption. The finite-type hypothesis supplies the finite support of each
coefficient family. The proof chooses a split-torus isomorphism, restricts
the given action along its inverse followed by j, and transports the
character coefficient family along the induced additive lattice
equivalence. The weight membership, singleton and sum formulas survive
this reindexing and give the claimed decomposition.

This is an extension of the implemented proof route in the published
`Torus.UniversalAdjointCoefficients` and `Torus.WeightDecomposition`
modules. It reuses their actual universal point, character coordinates,
translated evaluation, and the existing finite coefficient reconstruction;
it replaces conjugation by the published differential of the supplied
automorphic action. No structural existence, smooth representability,
semigroup subgroup equality, or split-unipotence result is asserted here.
