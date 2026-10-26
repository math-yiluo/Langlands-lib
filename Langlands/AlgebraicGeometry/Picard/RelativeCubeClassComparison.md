# Rigidified class comparison from ordinary relative cube triviality

This internal categorical adapter converts a supplied ordinary three-face
cube triviality principle into two-axis equality detection for actual
relative rigidified line-bundle classes. It works in every scheme universe
over an arbitrary base scheme, with arbitrary pointed objects `X`, `Y`, and
`Z` in `Over S`. It supplies no geometric cube theorem.

The geometric input is explicit: every actual line bundle on
`(X ⨯ (Y ⨯ Z)).left` that is ordinarily trivial on the three existing
`CubeFace` maps is ordinarily trivial on the whole product. The conclusion
uses the existing `RigidifiedLineBundle.Classes` quotient and the actual
`classesPullback` maps along `CubeFace.secondAxis` and `thirdAxis`.
The second axis fixes the `Y` coordinate; the third axis fixes the `Z`
coordinate. The rigidification fixes the `X` coordinate. All comparisons
are on full schemes, including nonreduced parameter schemes.

`CubeRelativeTransport.cubeFirst_inv_prodIso`, `cubeSecond_inv_prodIso`,
and `cubeThird_inv_prodIso` invert the existing product/relative-space
comparison equations. They express each actual face followed by the
inverse `relativeSpaceProdIso` as the corresponding relative section or
relative axis map, preceded in the latter two cases by the smaller product
comparison's inverse. Their proofs insert the relevant isomorphism and
cancel it using the published forward equations.

`CubeRelativeTransport.relativeTrivializationOfCubeTriviality` transports
an actual line bundle `D` from the relative space to the ordinary product
by pullback along `relativeSpaceProdIso.inv`. The first inverse face equation
and the existing module pullback composition/congruence comparisons
transport a section trivialization to a first-face trivialization.
`pullbackSquareTrivialization` and the other two inverse equations do the
same for the axis restrictions. Classical choice selects the ordinary
trivialization supplied by the stated cube criterion.
`recoverTrivialization` along the inverse product comparison transports it
back to `D`. No descent theorem or geometric assumptions enter this step.

`RigidifiedLineBundle.classes_eq_of_threePullbackTriviality` is a more
general adapter for two arbitrary relative restriction maps into one
parameter scheme. It assumes the existing local-rank-one/tensor-invertibility
comparison on the ambient relative space, canonical pullback-tensor
preservation, and ordinary triviality detection by the relative section
and those two restrictions. Quotient induction chooses representatives
`L` and `M`. Equality of each restriction class supplies an actual
rigidified isomorphism, whose underlying module-sheaf isomorphism is used.
Their rigidifications supply the third ordinary comparison along the
section. The published `lineBundleIsoOfThreePullbackComparisons` constructs
an ordinary carrier isomorphism. The published
`RigidifiedLineBundle.isoOfCarrierIso` adjusts it to respect the specified
rigidifications, using the relative projection as a retraction of the
relative section. The resulting compatible isomorphism proves equality
in the original quotient. The construction does not assert that its
isomorphism extends the chosen restriction witnesses.

`rigidifiedClasses_eq_of_cubeTriviality` combines these two adapters for
`T = Y ⨯ Z`. It retains the ordinary cube triviality principle, canonical
tensor preservation, and the local tensor-invertibility comparison as
explicit hypotheses. Specializing to abelian schemes consequently requires
an independently proved geometric cube theorem and proofs of the tensor
inputs. This result alone proves neither the unconditional relative cube
statement nor Mumford parameter additivity.

The provenance is internal: the implementation composes the accepted
`CubeRelativeTransport`, `CubeIsomorphismAssembly`, and
`RigidifiedCarrierIso` interfaces and their categorical pullback/product
identities. It introduces no original-source geometric assertion and
changes no published statement or import. Author: Worker 579.
