# Norm-one root reflections and special-point fixed loci

This is an internal deduction on the published actual valuation-building data.
It uses the existing actual rational-point action and apartment, rather than
introducing a different building or action. The construction is conditional on
the explicitly retained hypotheses described below. It does not construct
valuation-building data, a metric, a canonical integral model, or the comparison
with a supplied integral model.

`ValuationBuildingData.NormOneAffineRootReflection B ψ` records an actual
normalizer point, a vector paired to two by the derivative of `ψ`, membership of
the underlying rational point in the common rational-character norm kernel,
and equality of the actual apartment action with the corresponding affine
reflection. `normOneAffineRootReflection` chooses such data for every affine
root under topology compatibility (V 7) and the existence-only predicate
`RelativeRoot.HasOppositeFactorPairs B.i`.

Every actual root point belongs to a filtration at the finite real depth
obtained from its apartment valuation by `untopD 0`; the inequality needed for
membership also holds for the identity, whose value is infinity. The published
compact-filtration norm-kernel inclusion then proves that the entire root
group is norm one. For an actual opposite pair, the published Weyl-action
formula proves that the negative character is again a root. Both opposite
factors and the original root point are therefore norm one, so their actual
product is norm one. The published root-reflection action identifies the
product's action with its geometric reflection. These steps use no
surjectivity assertion for a central cover.

For an affine root that vanishes at an apartment point `x`, its chosen lift
belongs to the existing `compactStabilizer (B.apartmentMap x)`: it is norm one
and its reflection fixes `x`. If the apartment map is injective, any apartment
point whose image is fixed by this lift lies on the same root hyperplane.
Indeed, injectivity makes the affine reflection fix the point, and applying
the root gives a real number equal to its negative.

The generic affine-root-system lemma
`AffineRootSystem.eq_of_isSpecialPoint_of_vanishingRoots` proves that a point
where all roots vanishing at a special point also vanish equals that special
point. Specialness identifies each derivative kernel with a kernel from a
root vanishing there. The difference of the two points lies in all these
kernels. Derivative spanning and separation by the algebraic dual force that
difference to be zero. This argument also includes rank zero.

The resulting apartment-local uniqueness theorem retains V 7, actual opposite
pair existence, the rank-zero-compatible affine-root-system axioms, and
injectivity of the actual apartment map. Its final corollary obtains the first
and third premises from `B.SatisfiesApartmentAxioms` and states uniqueness in
the base apartment image for the existing norm-one stabilizer at a special
point. No common-apartment coverage or global uniqueness is asserted here.
No residue-cardinality restriction is introduced.

The provenance is internal: the proof combines the published
`ApartmentRootReflections`, `KPParahoricFixerComparison`,
`RootFactorizationFromExistence`, affine-root-system definitions, and Mathlib
linear algebra. Its route is described above; no additional external
literature theorem is imported or assumed.
