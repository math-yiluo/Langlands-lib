# Characters reconstructed from natural affine unit values

Author: Worker 706; verified and documented for the exact descent proof by
Worker 1366. This is a derived internal construction using the existing
Library corepresentation interface.

Let `F : Type u` be a field and let `H` be any affine group scheme over
`Spec F`. Suppose that for every `A : CommAlgCat.{u} F` a group homomorphism
`α A : H.affinePoints A →* Aˣ` is given, and that these homomorphisms commute
with every morphism of test algebras. No finite-type, commutativity,
smoothness, connectedness, reductivity or splitting assumption on `H` is
needed.

The construction `character H α hα` is an actual member of
`rationalCharacters H`: a group-scheme morphism from `H` to `Gm`, expressed
in the existing additive character convention. To construct it,
`coordinateApp` transports the proposed values through
`AffineCoordinates.actualPointsEquiv` for the source and target, and
`Gm.affineUnitsEquiv` for the target units. `coordinateNat` proves this is a
natural transformation of the corepresented group functors. Its naturality
proof uses the supplied `hα` together with naturality of the two existing
comparisons.

`Corepresented.groupSchemeMap` turns that natural transformation into a
morphism of the corepresented group schemes. The existing
`AffineCoordinates.groupSchemeIso` maps transport it back to `H` and the
actual multiplicative group. Affineness of that multiplicative group is
inferred from its existing pullback construction.

`character_values` proves the prescribed value formula on every affine
test algebra: applying `Gm.affineUnitsEquiv` to the image of any point
`y : H.affinePoints A` under the constructed character gives `α A y`.
The proof uses `Corepresented.groupSchemeMap_affinePoints`, the comparison
with actual affine points, and cancellation of the transport isomorphisms.
This formula concerns all affine test algebras in the indicated universe.
