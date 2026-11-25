# Actual jet frames adapted to affine cotangent frames

This module constructs actual free frames of the identity-jet sheaf
from an actual cotangent frame on an affine base open. Let `G` be a smooth
affine group scheme over an arbitrary scheme `S`, let `U` be an affine
open, and specify a finite-index actual free sheaf frame `e` of
`G.cotangentAtIdentity` on `U`.

`cotangentFrameBasis` transports the actual section basis of `e` on any
affine `V ≤ U` through the canonical equivalence with the augmentation
cotangent. `cotangentFrameBasis_restrict` uses the earlier intrinsic
restriction comparison and actual section-basis naturality.
`cotangentRestrictionMatrix_frame` consequently says that the cotangent
restriction matrix in these bases is the identity.

Choose augmentation-ideal lifts `z` of the cotangent basis on `U`.
The definition `adaptedSectionBasis` transports the algebraically chosen
total adapted jet basis to the actual sections `Γ(IdentityJet.module G n,U)`.
Its index is the previously defined finite type `JetIndex σ n`. These
choices use only the original cotangent frame and the specified lifts;
the algebraic total basis uses the existing chosen linear truncation
sections.

The theorem `exists_restricted_adaptedSectionBasis` proves that restriction
of this family remains a basis on every affine `V ≤ U`. Choose any target
cotangent lifts on `V` and the resulting algebraic total basis. The actual
semilinear restriction determinant formula gives determinant one for the
source vectors in that target basis, since the cotangent matrix is the
identity. The arbitrary-ring unit-determinant criterion makes these
restricted vectors a basis. The intrinsic jet section comparison then
transports this basis to the actual sheaf sections.

The generic `affineBasisFrame` construction applies to these actual
restricted section bases and gives `adaptedFrame`, an isomorphism from
the actual finite free sheaf to the actual jet module on `U`.
`adaptedFrame_basis` computes its section basis on every smaller open as
the actual restriction of the originally specified adapted affine basis.

The provenance is internal. The construction combines actual cotangent
and jet section comparisons, the already proved splitting-independent
restriction determinant, and the sheaf criterion from affine subopens.
The existence of a supplied finite cotangent frame on this chart does
not impose a global constant-rank condition. This module constructs the
required local jet frames; it does not glue a determinant-power
line-bundle isomorphism or prove ampleness.
