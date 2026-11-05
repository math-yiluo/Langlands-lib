# Cartier smoothness for actual affine group schemes

Author: Worker 1609. The imported algebraic port is by Worker 133.
The underlying scheme-isomorphism expression also occurs in Worker 1371's
affine-image coordinate adapter and is reused here.

`Langlands.GroupScheme.affineCartierSmooth.{u}` proves precisely
`Langlands.GroupScheme.AffineCartierSmoothStatement.{u}`. The field has
characteristic zero and arbitrary universe `u`; the group scheme is actual,
affine over that field and locally of finite type. No further group or field
hypothesis is retained.

The implemented proof uses the published affine-coordinate constructions.
`AffineCoordinates.hopfAlgebra G` is the commutative coordinate Hopf algebra
of `G`, and `AffineCoordinates.algebraFiniteType` gives its finite type from
local finite type of the structure morphism. The algebraic Cartier theorem
`HopfAlgebra.isReduced_of_finiteType_of_charZero` makes this algebra reduced.
Taking spectrum and transporting through `AffineCoordinates.hopfSpecIso`
then proves reducedness of the actual underlying scheme.

For each field `K` and morphism `y : Spec K → Spec k`, the coordinate ring map
`Spec.preimage y` is an injective map from the field `k`. Thus `K` also has
characteristic zero. The actual base change of `G` along `y` is again affine
and locally of finite type. Applying the preceding reducedness argument to
this group proves `GeometricallyReduced G.X.hom`, using Mathlib's criterion
that all field-valued pullbacks are reduced. Finally Mathlib's
`AlgebraicGeometry.smooth_of_grpObj` proves smoothness from geometric
reducedness and local finite type, retaining the actual group-object data.
The helpers `AffineCartierSmoothProof.isReduced` and
`AffineCartierSmoothProof.geometricallyReduced` implement these two steps.

The original mathematical target is Cartier's theorem, Milne, *Algebraic
Groups* (2017), Theorem 3.23, printed p. 71 (PDF p. 87), with supporting
Lemmas 3.19–3.22 on printed pp. 70–71. These pages and the complete registered
author-errata snapshot dated 2026-11-02 were read; the errata change neither
the theorem nor these lemmas. The Lean proof uses the algebraic Cartier
implementation in the Anthropic FLT port and the existing geometric group
smoothness theorem. The source and compatibility details of the imported
algebraic proof are documented in its own paired modules. This file's
coordinate transport, field-base-change argument and final assembly are
internal derivations from those interfaces. No target statement or its
imported files is changed.
