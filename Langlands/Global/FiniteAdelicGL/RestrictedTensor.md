# Restricted tensor representations of finite adelic general linear groups

This internal construction specializes the published restricted tensor action to
`FiniteAdelicGL F n`, the actual matrix-unit group over the finite adeles of the
number field `F`, with its existing topology. It uses the proved continuous
multiplicative equivalence `restrictedProductEquiv F n` with the restricted
product of the actual completed-local groups relative to `localIntegral F n v`.

The coefficient field `K`, the number field `F`, and the local carrier universes
are independent. Every natural rank `n` is allowed, as are infinite-dimensional
local vector spaces. The local representations are supplied as genuine linear
representations of `FiniteLocalGL F n v`.

## Construction and scope

`tensorRepresentation` acts on the actual algebraic direct limit
`RestrictedTensor.Space K V E e`. Outside the finite exceptional set `E`, the
reference vector `e v` must be fixed by the actual integral subgroup. It first
uses `RestrictedTensor.representation`, then composes with the monoid homomorphism
underlying `restrictedProductEquiv`. The representation laws and well-definedness
therefore follow from those established constructions.

This general version allows zero reference vectors. The usual nonzero-reference
version `restrictedTensorRepresentation` uses `ReferenceVectors V E` and the
existing `Product K V E r`. Only the references outside `E` must be nonzero;
no vector is required at an exceptional place. The unused coordinates of the
family are filled with zero by the existing constructor.

`tensorRepresentation_pure_of_mem` states that an adelic element acts
componentwise by its actual local projections on any finite tensor stage outside
which the element is integral. Such stages can always be obtained by enlarging a
stage, since `eventually_localIntegral` gives only finitely many exceptional
places. This formula follows directly from the generic same-stage action formula.

`tensorRepresentation_localInclusion` identifies the operator of the actual
identity-supported local inclusion with the generic `mulSingle` operator. Its
proof rewrites by the arithmetic equivalence's local-inclusion identity. The
corresponding pure-tensor formula updates only that coordinate on every stage
containing the place. Its proof uses that the projection at that place is the
given matrix and every other projection is one, by `localProjection_localInclusion` and
`localProjection_localInclusion_of_ne`. Outside the stage this gives the integral
membership needed for the same-stage formula.

The two smoothness theorems assume smoothness of each local representation in
the existing `Langlands.IsSmooth` sense. The generic theorem uses openness of the
integral subgroups to produce open stabilizers, and `isSmooth_comp` pulls them
back along the continuous arithmetic equivalence. No topology on the vector
spaces, finite-dimensionality, or admissibility hypothesis is used.

`tensorIntertwiner` takes genuine component intertwiners, allowed between
families with different carrier universes and exceptional sets. It assumes that
their reference vectors agree after applying these maps at all but finitely many
places. Its underlying map is the published restricted tensor map. The generic
`map_intertwines` identity, evaluated at the adelic element's restricted family,
proves that it intertwines the actual finite adelic actions.

## Provenance and remaining obligations

This unit is an internal specialization of the published modules
`Global.FiniteAdelicGL.RestrictedProduct`, `Representation.RestrictedTensor.Action`,
`Representation.RestrictedTensor.Smooth`, and
`Representation.Smooth.Transfer.PullbackProof`. It introduces no new assertion
from external literature. The algebraic direct-limit construction and its
literature provenance remain in `Representation.RestrictedTensor.Basic`.

The result constructs a representation from specified local factors. It does not
assert that an automorphic representation has such a factorization, nor provide
local-component existence or uniqueness, admissibility, irreducibility, a Hilbert
completion, or an archimedean action. Those are separate obligations.
