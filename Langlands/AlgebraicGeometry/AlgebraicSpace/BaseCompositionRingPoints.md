# Ring-valued fibres after composition of bases

Author: Worker 109.

This internal construction derives point-fibre comparisons from the actual
base composition and the published restriction-of-scalars test-scheme
isomorphism. No external literature assertion is claimed as proved.
All rings, schemes and test schemes retain arbitrary universe `u`, with
space points valued in `Type (u+1)`.

Let `D,C,A : Type u` be commutative rings with compatible actions
`D → C → A`, expressed by the algebra structures and `IsScalarTower D C A`.
For a space `X` over `Spec C`, `ringPointLift D C A X` maps its actual
`C`-relative `A`-points to `D`-relative `A`-points of
`space (Spec.algebraMap D C) X`. It first uses `liftSection` on the original
`ringTest C A`, retaining the original structure-map coordinate. Then it
pulls back along the inverse of `ringTestRestrictScalarsIso D C A`, which
identifies that same spectrum viewed over `D` with `ringTest D A`.
The scalar-tower equation justifies this test-scheme comparison.

`ringPointLift_injective` combines injectivity of `liftSection` with the
bijective map induced by an isomorphism of test schemes.
`ringPointLift_map` proves compatibility with every original space morphism
using naturality along the test isomorphism and `map_liftSection`.

`fibreTestIsoEquiv` identifies section fibres under any isomorphism of test
schemes. Its underlying section bijection is the presheaf image of the
inverse test isomorphism; naturality and injectivity of the corresponding
target bijection show that it preserves and reflects the fibre equation.

`ringPointFibreEquiv` composes the published `fibreEquiv` for base-composed
presheaves with this test-isomorphism equivalence. Thus, above any target
of the form `ringPointLift D C A Y y`, every point of the composed source
fibre corresponds to exactly one original `C`-relative point of the original
source fibre over `y`. The fixed target forces the original structure-map
coordinate to agree with the prescribed `C`-action. No surjectivity of the
point lift onto all composed points is assumed or asserted.
`card_ringPointFibre` gives equality of the two natural cardinalities via
this equivalence, without any finiteness assumption.

This comparison can transfer a bound on composed fibre cardinalities back
to the original coefficient action. It does not itself prove such a bound,
a uniform finite-field estimate, or the unconditional adelic openness target.
