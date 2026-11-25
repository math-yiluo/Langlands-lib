# Actual recovered reductive quotients at unramified fixed facets

This is an internal construction from published Library results. Its entry
proposition is
`Langlands.Geometry.Building.KPApartmentData.UnramifiedFixedFacetRecoveredQuotientStatement`.
The theorem `unramifiedFixedFacetRecoveredQuotients` proves that proposition in
arbitrary universe `u`, without a characteristic restriction.

Let `F` be a nonarchimedean local field. Supply a Galois-stable apartment datum
for a maximal split torus of the extended connected reductive group, the
centralizer and integer-valuation compatibility, and actual
`IntegerFacetModelData` over `fixedFieldIntegers F`. The full models must have
the stated integral-point formula: the character-valuation kernel intersected
with the pointwise fixer of the facet. Supply an original `GaloisFacet E`.
Geometric connectedness of the original `F`-group then gives:

- an actual downstairs `RelativeComponentModelData N0` over the integers of `F`
  and an `UnramifiedComponentModelRecovery` of the given upstairs model at `E`;
- actual downstairs `SpecialFibreQuotientData P0` satisfying
  `P0.IsReductiveQuotient`;
- a constructed valid upstairs reductive quotient whose quotient group scheme
  is literally the residue base change of `P0.quotient`;
- the literal canonical coefficient square and all-test incident-facet image
  covariance for this constructed quotient, with identity quotient
  identification.

The model family, apartment, full integral-point formula and geometric
connectedness remain hypotheses. The construction chooses the upstairs
quotient; it makes no uniqueness claim about another supplied quotient.

The generic constructor
`SpecialFibreQuotientData.recoveredBaseChange` starts with actual downstairs
quotient data and an isomorphism from the base change of its neutral special
fibre to an independently given upstairs neutral special fibre. The radical is
the base changed radical, its inclusion is followed by the isomorphism, and
the projection is the inverse isomorphism followed by the base changed
projection. The quotient is the literal base change. Affineness follows from
base change of the affine structure map.

For a separable residue extension,
`recoveredBaseChange_isReductiveQuotient` proves the three clauses of actual
quotient validity. The published
`SeparableUnipotentRadical.isUnipotentRadical_baseChange` identifies the base
changed radical, and `IsUnipotentRadical.comp_iso` transports it to the actual
upstairs source. Smoothness, affineness and connectedness of the downstairs
source come from the neutral model's smoothness and connected fibres.
`RelativeRoot.IsFppfQuotient.baseChange` and `.comapIso`, together with the
all-test range transport identities, give the fppf quotient clause.
`IsConnectedReductive.baseChange_of_algebraicExtension` gives connected
reductivity. Separability supplies algebraicity.

In the canonical specialization the original residue field is finite and
therefore perfect. The published `fixedFieldResidueIsAlgClosure` supplies
algebraicity and algebraic closedness upstairs, so the residue extension is
separable. `IntegralModel.residueRecoveryIso` provides the actual source
isomorphism. Thus `unramifiedFixedFacetRecoveredQuotient` is actual quotient
data of the supplied model at `E`, and its validity follows from downstairs
validity. Its projection is definitionally the recovered map
`unramifiedFixedFacetDescendedMap`.

The published `unramifiedFixedFacetDescendedMap_naturality` proves the
canonical quotient coefficient square with this projection and identity
quotient identification. Applying `unramifiedFacetResidueComparisons` to that
square gives `HasGaloisResidueImageCompatibility` for the actual all-test
images of incident facets. These maps use the original fixed-facet residue
comparison and the canonical residue coefficient action.

Finally, the proof obtains actual component recovery from the published
`exists_unramifiedFixedFacetRecovery`. It selects a downstairs quotient using
`SpecialFibreQuotientData.exists_isReductiveQuotient` over the perfect original
residue field, then combines validity, the coefficient square and image
covariance. A private helper isolates quotient selection from the large
fixed-facet context; this does not add a mathematical hypothesis.

The direct Library inputs are `UnramifiedRecoveredFacetMaps`,
`ReductiveQuotientExistence`, `SeparableUnipotentRadicalProof`,
`FppfQuotientComparison` and `Reductive.AlgebraicExtensionAscent`, as imported
in the Lean file. This module composes those constructions and does not assert a
separate theorem from the literature. The remaining argument for the
fixed-point split-torus statement requires an
actual facet-parabolic correspondence, residue tori and their lifts, and the
apartment and unit-fixation argument. It does not prove
`UnramifiedFixedPointSplitTorusStatement`.
