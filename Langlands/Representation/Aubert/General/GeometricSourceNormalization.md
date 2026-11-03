# Ambient normalization of the actual geometric source term

This internal construction specializes `LeviJacquetNormalization` to the
literal source intersections in the published `GeometricK0Target`. Its
provenance is those actual definitions and their proved same-radical Haar
transport. It introduces no structural realization or representation premise.

For arbitrary subgroup families `P`, `M`, `U`, subsets `I`, `J`, and every
ambient element `n`, the source Levi is
`M J ∩ n⁻¹ (M I) n` and the source radical is `M J ∩ n⁻¹ (U I) n`.
The supplied `GeometricSourceDecomposition` says these form the actual
semidirect decomposition inside `M J`. Both ambient subgroups lie in `M J`
by their literal intersection definitions.
`geometricSourceLevi_le_normalizer` applies `normalizes_of_subgroupOf`
to these two containments and the decomposition's inside normalizer law.
Thus the ambient normalizer inclusion is derived.

`geometricSourceAmbientJacquetFunctor` is actual trivial-character
localization by the source radical restricted to `M J`, followed by
pullback along the inverse of the actual output subgroup identification,
then the ambient inverse half-Haar-character twist of that same source
radical. The radical's closedness follows from the supplied closedness of
`U I` and `M J` and continuity of conjugation.
`geometricSourceJacquetAmbientIso` specializes
`leviNormalizedJacquetAmbientIso` to identify this presentation with the
published actual source Jacquet functor. Its component is the identity
linear map on the original localization carrier.

`geometricSourceInverseHalfCharacter_eq` specializes the proved
`leviInverseHalfCharacter_eq` at every element of the actual source Levi.
Closedness of `M J` supplies its locally compact topology. The equality
compares the same radical in the containing Levi and in the ambient group;
it is proved without a character-compatibility premise.

`geometricTermSourceAmbientFunctor` composes this source presentation with
the published forward conjugation and the published actual target normalized
induction. In particular, the transport still acts by `σ(n⁻¹ x n)`, and the
target normalization is unchanged. `geometricTermSourceAmbientIso` is the
right whiskering of the source isomorphism by these two actual functors.
Its final components are the images of the source identity maps under the
same conjugation and induction functors.

For finite-length input, `geometricTermSourceAmbient_hasFiniteLength`
transports the published term's finite-length proof along this actual
isomorphism. It requires only the existing `GeometricTermFiniteLength`
premise. `geometricTermK0_ofSourceAmbient` first applies
`geometricTermK0_ofRepresentation`, then equates the two classes using
`FiniteLengthGrothendieckGroup.ofObject_eq_of_iso`. The Grothendieck group
retains its defining relations from all actual finite-length short exact
sequences. This is a comparison with the published actual term map, not
an arbitrary class equation.

The indexing, group, and carrier universes are independent. The source
comparison uses the full smooth categories with carrier universe `uV`;
the composite and class formula use the same `max uG uV` saturation as the
published geometric term. There is no Weyl-minimality assumption or choice
of a lift here, so the comparison applies to every actual normalizer lift
in the rational-point target. There is no general-linear specialization.

The proof bodies depend on the published actual intersection functors,
the same-radical Haar normalization comparison, functorial whiskering,
finite-length transport under an actual smooth isomorphism, and equality
of classes under such an isomorphism. They use no geometric lemma,
adjointness, cuspidal support, character independence, or classification
theorem. The import closure includes the broader representation
infrastructure and `GeneralLinearDerivativeDeterminantTwistProof` through
`LeviJacquetNormalization`; the latter uses only that module's generic
pullback/twist isomorphisms.

This construction does not identify a geometric orbit graded piece, construct
the required geometric filtration, compare compact with full induction,
establish either orbit Haar correction, balance different radicals, or prove
the rational-point geometric K0 expansion. Those obligations are retained.

Author: Worker 1263.
