# Finite vertex approximation from closed-facet fixation

This internal construction works with supplied `IntegerValuationBuildingData`
over any field at universe `u`. The corrected affine root system is an explicit
premise. `facetClosureVertexFinset` is exactly the image in the original
translated apartment of the vertices of all closed facets meeting an affine
bounded subset. It is nonempty when that subset is nonempty, and every image
point is an actual vertex in the existing quotient-building sense.

The construction applies `AffineRootSystem.boundedFacetVertexFinset`, then takes
its image under the original translated apartment map. The metric needed only
for that finite apartment construction is the published norm pulled back from
the finite set of actual relative roots. Splitness and connected reductivity
give root finiteness; the injective root-coordinate map gives finite
dimensionality. No metric or local-field structure on the base field or the
quotient building is asserted.

`extendedAffineRoot_mem_or_two_smul_mem` derives AS4 from the actual rank-one
factorization of the maximal split torus in the connected reductive group and
the published opposite-pair doubling theorem. It is not an additional input.
The membership equivalence with `KPApartmentData.facetClosureVertexImage` and
its published fixer-invariance theorem then show that every pointwise fixer of
the translated subset preserves this finite set.

The final theorem has one further geometric premise:
`B.ClosedFacetsFixedByVertices`. This premise says that an original rational
element fixing the quotient images of every vertex of a closed facet fixes
its entire quotient image. The premise is not proved in this module.

For containment, a member of the finite intersection of one-stabilizers lies
in the character-valuation kernel and fixes every vertex image. Conjugating
by the apartment translation gives an element fixing all base-apartment
vertices of the closed facet through each point of the original subset.
The geometric premise fixes that point, and translating back proves
containment in the original norm-one pointwise fixer.

Finally that fixer is a subgroup of the character kernel and preserves the
finite vertex set. `normal_finiteIndex_iInf_oneStabilizer` identifies its
subgroup of common vertex fixers with the kernel of its actual finite
permutation action, proving normality and finite index. The separate
containment proof prevents `subgroupOf` from hiding a larger intersection.
All fixers and actions are those of the original rational-point group on
the original quotient.

This is a conditional reduction toward maximal-unramified finite vertex
approximation. It does not discharge the corrected affine-root-system or
closed-facet fixation premises and does not prove the unconditional target.
