# Indivisible lifts of all derivatives in actual quasi-split apartments

Author: Worker 244, Task 6506.

`Langlands.Geometry.Building.quasiSplitIndivisibleDerivativeLifts` proves
exactly the published proposition
`QuasiSplitIndivisibleDerivativeLiftsStatement.{u}`, at every universe `u`.
The statement module is imported unchanged.

For a henselian field with a surjective integer-valued valuation, an actual
affine quasi-split group and a prescribed maximal split torus, the conclusion
holds for every supplied apartment datum with full centralizer compatibility.
Every member of the full derivative set has an affine lift whose half is absent
from the actual affine roots. Multipliable derivatives remain in the
conclusion. There is no restriction on the field characteristic, residue
characteristic or residue perfection, and no completeness hypothesis.

## Implemented proof

The proof is the application

```
algebraicRankOneIndivisibleLiftsReduction algebraicRankOneCoordinatesExistence.
```

Both terms are published Library theorems. The first, in
`QuasiSplitHenselianUnitaryDepths`, has type
`AlgebraicRankOneCoordinatesExistenceStatement.{u} ->
QuasiSplitIndivisibleDerivativeLiftsStatement.{u}`. The second, in
`AlgebraicRankOneCoordinatesExistenceProof`, discharges its entire premise at
the same universe. The resulting theorem retains no extra premise.

Here is how the imported reduction obtains the claimed lifts.

1. Connected reductivity and maximal splitness give actual opposite-factor
   pairs and the bound excluding fourth root multiples. A multipliable root
   is therefore indivisible as a relative root. Quasi-splitness makes the
   supplied full centralizer a torus.
2. The algebraic existence theorem provides coherent opposite-root coordinates,
   a common SU3 homomorphism, an actual coroot morphism and a Weyl image in the
   normalizer for each multipliable root. Its finite separable quadratic tower
   is an output, not an additional field hypothesis.
3. `AlgebraicSU3RootCoordinates.exists_unitaryTowerDepths` uses a point of the
   supplied apartment fixed by the Weyl image. Actual opposite-factor
   identities, full centralizer compatibility and norm calibration of the
   henselian separable extension valuation identify the root depth there with
   the original base-normalized unitary tower depth. This works directly in
   the supplied arbitrary apartment; no canonical-apartment premise is used.
4. `SU3Root.tower_hasIndivisibleCentralJump` supplies a central depth jump whose
   half is absent from the quotient jumps. The coordinate comparisons in
   `CoordinateAffineRootJumps` and `UnitaryDoubleAffineRootJumps` convert it to
   an indivisible actual affine root in the doubled direction.
5. For a derivative having no half relative root, every affine lift already
   has no half affine root. For a derivative having a half relative root, the
   preceding unitary construction supplies the required lift. The final
   theorem in `UnitaryIndivisibleAffineLifts` makes this case split over the
   full derivative set.

Thus this proof uses the published rank-one coordinate and finite-tower jump
route rather than constructing a separate canonical global valuation class.
The algebraic existence theorem itself composes the published absolute-root
product and adjacent-simple-root SL3 constructions with their Galois-descent
assemblies. The dependency route uses no local anisotropic classification,
local rank-one classification or local Kneser–Tits result.

## Provenance

This is a closed composition proving an unchanged published derived target.
Its original-source correspondence remains in
`QuasiSplitIndivisibleDerivativeLiftsStatement.md`: Kaletha–Prasad (2023),
Chapter 6, Definition 6.3.4, Proposition 6.4.8, Remark 6.4.9, Table 6.4.1 and
Proposition 6.2.6, with the 2024 corrections on PDF p.32. The implemented
rank-one proof is described above and in the paired Markdown of the imported
construction modules. It covers the exceptional nonreduced case through the
central-versus-quotient jump comparison without deleting doubled derivatives.
