# Linear quotient affineness from geometric reductivity

Worker 690.

`ReductiveLinearQuotientAffine.affineModelIso` constructs the canonical scheme isomorphism from the original supplied homogeneous quotient to the spectrum of its own global section ring. It assumes the full proposition `ReductiveGeometricReductivityStatement.{u}`, an algebraically closed field `k : Type u`, an actual connected reductive group `G`, any natural number `N`, a closed representation `ρ : G → GL_(Fin N)`, and a supplied `Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient ρ`. Its forward morphism is precisely `Q.scheme.left.toSpecΓ`, as proved by `affineModelIso_hom`. No alternative quotient is chosen. The isomorphism here is of underlying schemes.

The supporting theorem `reductiveLinearQuotientAffine_of_geometricReductivity` proves
`ReductiveGeometricReductivityStatement.{u} → ReductiveLinearQuotientAffineStatement.{u}`.
Both Library propositions remain unchanged. The reduction retains arbitrary characteristic, every universe, all natural dimensions including zero, and the supplied quotient with its exact coset fibers on every relative scheme test, including nonreduced and nonaffine tests.

The proof first uses the published `IsConnectedReductive.isPseudoReductive` theorem on the same group. Smoothness and affineness are already fields of its connected-reductivity hypothesis. Applying the assumed geometric-reductivity statement gives the single-group predicate `IsGeometricallyReductive G`. The ambient general linear group is affine for every dimension. The generic theorem `HomogeneousQuotientFromEmbedding.HomogeneousQuotient.isAffine_of_geometricallyReductive` then proves affineness of the original quotient scheme; hence its structure morphism is affine. Finally Mathlib's `Scheme.isoSpec` gives the canonical isomorphism selected by the definition.

Provenance is internal and derived from these published interfaces and the supplied-quotient invariant-theory development. The generic affineness argument constructs affine principal neighborhoods, extracts a finite ambient unit certificate, obtains the unit ideal in all-test invariant functions by homogeneous polynomial coefficients, descends through the actual quotient section-ring equivalence, and applies the affine principal-open criterion. No existing unconditional Haboush implementation, regular-cocharacter/Borel proof, classification result, or excluded rank-one input is used in this reduction.

This is a conditional reduction and construction. It does not prove `ReductiveGeometricReductivityStatement`, discharge the independent geometric-reductivity prerequisite, or prove the host task's unconditional `ReductiveLinearQuotientAffineStatement`. An independently accepted proof of the full geometric-reductivity statement remains necessary for that task.
