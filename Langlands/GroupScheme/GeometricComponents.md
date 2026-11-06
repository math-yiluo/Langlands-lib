# Chosen geometric components with continuous absolute Galois action

This is an internal derived construction from the published
`AlgebraicallyClosedComponents` and `ComponentGaloisContinuityProof` interfaces.
It adds a chosen geometric object and its functorial absolute Galois action;
it uses no new external structural assertion.

For a field `k : Type u` and an actual group scheme `H` over `Spec k`,
`GeometricComponents k H` is the full connected-component space of the actual
pullback of `H` to Mathlib's chosen `AlgebraicClosure k`. Its topology is the
existing connected-component quotient topology. That topology is T1 even before
the smoothness and affineness hypotheses below.

If `H` is smooth and affine over `k`, the published algebraically closed component
construction supplies a finite group structure on this carrier. Its actual
quotient topology is discrete. The hypotheses imply finite type here: smoothness
supplies local finite presentation and affineness supplies quasi-compactness.
No connectedness, reductivity, perfection or characteristic assumption is imposed.
The field and all schemes retain the arbitrary universe `u`.

`geometricComponentOfPoint` is the group homomorphism from actual sections over
the chosen algebraic closure to their actual scheme components. Its surjectivity
is the published rational representability theorem over an algebraically closed
field; thus the construction includes every component.

`geometricComponentGaloisAction` specializes the existing coefficient action to
Mathlib's `Field.absoluteGaloisGroup k`, namely the `k`-automorphisms of the chosen
algebraic closure with their Krull topology. It defines a `MulDistribMulAction`.
The formula `geometricComponent_smul` identifies it with the semilinear
permutation of actual components, and `geometricComponent_smul_ofPoint` identifies
its value on a section's component with the component of coefficient conjugation
of that section. Multiplication and unit laws follow from the published action
homomorphism. Joint continuity is the published Krull-continuity theorem,
specialized to the algebraic extension `AlgebraicClosure k / k`; it is registered
as a `ContinuousSMul` instance for the inherited quotient topology.

For smooth affine `H` and `H'`, `geometricComponentMap k f` is a group
homomorphism induced by the actual base change of `f : H ⟶ H'`. Its evaluation
formula is the continuous map on components of that scheme morphism. The
identity and composition laws follow from the base-change functor and the
published component functor laws. `geometricComponentMap_smul` proves Galois
equivariance from coefficient-action naturality for an actual map defined over
`k`.

This file fixes the algebraic closure used by Mathlib. Comparisons along supplied
closure embeddings, their tower and equivariance laws, an étale group-scheme
realization, and descent or surjectivity assertions for base-field rational
points are separate obligations of the standing program. This construction
makes no embedding-independence or rational fixed-point surjectivity claim.
