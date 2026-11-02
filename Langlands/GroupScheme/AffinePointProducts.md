# Actual affine group points over a product coefficient ring

For a commutative base ring `R`, an affine group scheme `G` over `Spec R`,
and two commutative `R`-algebras `A` and `B`, this internal derived
construction identifies the existing actual point group `G(A × B)` with
`G(A) × G(B)`. The forward maps are induced by the two unital coefficient
projections. The inverse pairs the actual coordinate-algebra homomorphisms
and applies the existing affine scheme/algebra-point equivalence.

`affinePointPair_evaluation` proves that evaluating any global regular
function at the paired point gives the pair of its values at the original
points. Affine-point evaluation is injective, so this identity proves that
pairing and projection are mutually inverse. Each projection is a group
homomorphism by functoriality of actual coefficient extension. Therefore
`affinePointsProdEquiv` is a multiplicative equivalence for the original
point group structures.

If `A` and `B` have arbitrary topologies, `A × B` has their product topology.
Both projections are continuous by coefficient functoriality of the existing
evaluation topology. Pairing is continuous because every regular-function
evaluation is the pair of two continuous evaluations. Thus
`affinePointsProdHomeomorph` is a multiplicative homeomorphism for those
existing topologies. No continuity of the ring operations or the base
algebra maps is needed for this assertion. No finite-type, Hausdorff,
local-compactness or reductivity hypothesis is used.

The provenance is the universal property of product algebras and the
existing affine scheme/global-section equivalence, rather than a cited
structure theorem. This coefficient-product result supplies the product
of archimedean and finite adelic group points after specialization to the
actual adele coefficient ring. It does not identify finite adelic points
with a restricted product of local point groups or assert measure or
reduction results.
