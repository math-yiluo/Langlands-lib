# An etale atlas for the actual Picard class sheaf

`Langlands.AlgebraicGeometry.Picard.smoothAutomorphismEtaleAtlas.{u}` proves
the exact published proposition `SmoothAutomorphismEtaleAtlasStatement.{u}`.
For arbitrary actual schemes `S X : Scheme.{u}` and `f : X ⟶ S`, its
premises are the fpqc stack condition for `PicardGroupoid.relative f`,
`HasLocallyFiniteTypeSmoothSchemeAtlas f`, and
`HasSmoothRelativeAutomorphismSchemes f`. Its conclusion concerns the
literal ordinary presheaf `RelativePicard.etaleClassSheafPresheaf f`: it
has a scheme-representable diagonal and a surjective etale scheme atlas
whose scheme is locally of finite type over `S`.

The implemented proof applies
`smoothAutomorphismEtaleAtlas_of_smoothRelationQuotient.{u}`, from
`Picard.SmoothAutomorphismQuotientReduction`, to the published theorem
`AlgebraicSpace.smoothRelationQuotient.{u}`, from
`AlgebraicSpace.SmoothRelationQuotientProof`. The latter proves the whole
generic `SmoothRelationQuotientStatement.{u}`. This application discharges
the reduction's sole additional input at the same arbitrary universe.
The theorem's type is the unchanged Picard proposition.

The reused construction extracts an actual family from the smooth atlas
hypothesis. Its full arrow scheme has a kernel relation represented by
an actual scheme, with smooth projections supplied by the smooth relative
automorphism hypothesis. The first application of the generic quotient
theorem makes the canonical arrow-class sheaf an algebraic space and its
quotient map smooth and surjective. The published descent of smoothness
along smooth surjective source maps gives smooth projections of this
arrow-class equivalence relation on the object scheme.

The second application of the same generic theorem gives the quotient
of that relation a representable diagonal and a surjective etale scheme
atlas locally of finite type over `S`. The published local-surjectivity
theorem for the actual presentation supplies the comparison
`arrowClassQuotientPicardIso`, which identifies the complete quotient
presheaf with `RelativePicard.etaleClassSheafPresheaf f`. The construction
transports the diagonal and atlas through this natural isomorphism and
retains local finite type. The reduction accepts the target's stack
premise; its implemented argument already obtains the required properties
from the other two premises.

All scheme tests and slice morphisms remain in the full `Over S`, and
the comparison covers every sheaf section, including sections without a
global line-bundle representative. The geometric predicates retain
scheme representability on complete presheaf base changes. The resulting
theorem has exactly the three premises of the target, uniformly in `S`,
`X`, `f`, and `u`.

The provenance of this final proof is the internal composition of the
published reduction and the published generic quotient theorem. The
paired explanations of those modules describe their constructions and
source routes. This module implements the final application.
