# Minus one at a real place

This internal helper module is part of the proof development for the real-place
Rankin–Selberg functional equation. It proves that the minus-one element at a
real place acts by the Library's `realMinusOneScalar` on every actual cuspidal
operator realization. It does not prove the functional equation or identify that
scalar with a Langlands-parameter determinant.

The main construction is
`Langlands.Global.RankinSelbergGlobal.realPlaceMinusOneIntertwiner`.
For any operator realization `S` of `GL_n` and real place `v`, it is an
`S.Intertwiner S` whose underlying complex-linear map is
`S.realPlaceCompactRepresentation v (-1)`. Thus its intertwining property
refers to the full concrete operator algebra, rather than only the compact
subgroup at the place.

The inserted compact element is central in the full product of infinite compact
groups. Its actual adjoint on the real Lie algebra is the identity: the matrix at
the chosen real place is minus identity and all the other matrices are identity.
Scalar extension and the universal property of the enveloping algebra extend
this identity to the complex Lie algebra and its enveloping algebra.

The compact action therefore commutes with finite translations, all compact
translations and all enveloping operators. These three checks construct an
intertwiner of the whole concrete automorphic operator algebra. Its square is
identity.

For an irreducible representation, subtract identity from this intertwiner. The
result is either zero or injective. In the first case the original intertwiner
is identity. In the second case its value on `A x + x` is zero, because `A² = 1`;
injectivity gives `A x = -x`. Thus the action has a scalar, and the published
specification of `realMinusOneScalar` applies without an existence premise.
This argument requires no finite-dimensionality or global central-character
hypothesis.

The scalar-existence and action conclusions are respectively
`exists_realPlaceMinusOneScalar` and `realMinusOneScalar_action`. They apply
over every number field `F : Type u`, with the universe parameter free, under
the Library's ambient assumption `CompactSpace (AdeleQuotient F)`.
The generic algebraic lemma is
`intertwiner_involution_eq_one_or_neg_one`; its only representation-theoretic
assumption is irreducibility over `ℂ`.

All these statements are derived from the existing concrete actions and
irreducibility definitions; they are internal algebraic consequences, rather
than an additional theorem quoted from the analytic literature.
