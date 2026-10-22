# Finite-stage maps and lifted integer coefficients

Author: Worker 22. This interface imports the published canonical comparison
and its proof from `FiniteQuotientComparisonProof`.

`discreteStageToContinuous B A φ f q` sends actual ordinary cohomology of
a discrete topological group `Q` into actual continuous cohomology of `G`.
Here `B : TopRep k Q`, `A : TopRep k G`, `φ : G →ₜ* Q`, and
`f : TopRep.res φ B ⟶ A` is the specified continuous equivariant coefficient
map. The construction first applies the proved inverse of the canonical
`continuousToOrdinary B q` and then Mathlib's `ContinuousCohomology.map`.
Topology is forgotten only on the resulting cohomology morphism.
`comparison_comp_discreteStageToContinuous` verifies the defining
compatibility with that actual continuous map by cancelling the inverse.
The domain group may be any discrete group; finiteness is unnecessary.

Over a discrete commutative ring, `discreteTopRep B` equips an ordinary
representation `B : Rep k Q` with the discrete coefficient topology.
Continuity of the scalar action follows from discreteness of the ring and
module. Every representation operator is continuous, and its multiplicative
certificates are the original representation laws. `discreteTopRep_toRep`
verifies that forgetting this topology returns exactly `B`.
Consequently `ordinaryDiscreteStageToContinuous` has source exactly
`groupCohomology B q`. Setting `q = 2` gives the required map from finite
relative cohomology whenever the consuming Galois construction supplies
the quotient homomorphism and compatible coefficient map.

`additiveActionComparisonLinearEquiv` specializes the proved finite-quotient
comparison to the published `DiscreteModule.ofAdditiveAction`. The module
`M : Type u` is an additive commutative group with discrete topology and
a jointly continuous distributive action of the compact Hausdorff group
`G : Type u`. The coefficient ring is `ULift.{u} ℤ`; the comparison is a
linear equivalence over that ring in every natural degree. This explicitly
supports arbitrary coefficient universes without identifying the lifted
ring with an unlifted scalar object.

The provenance is derived from Serre, *Local Fields* (1979), VII §5,
printed pp.115–117 / PDF pp.121–123, and X §§3–4, printed pp.154–156 /
PDF pp.160–162: compatible maps, inflation, and the finite relative to
infinite Galois cohomology passage. The declarations implement those maps
using the separately proved canonical comparison. No local arithmetic or
field-unit module is constructed here.

Literature ID `serre-1979-local-fields`; SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`;
retained file `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Pinned environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

