# The first fundamental highest weight of the standard special-linear representation

This internal construction computes the actual diagonal-torus
character spaces of the column representation of the special-linear
group, for subsequent highest-weight recognition in the norm-one
normalization. It uses the published all-affine-test character-space
definition.

The restricted representation has the diagonal matrix of the published
torus entries on every affine test. Its original coordinates provide
separating character coefficients. Each coordinate vector belongs to
the space of its diagonal character. The coefficient comparison proves
that every occurring character is a diagonal character and that each
has multiplicity one, since the integral coordinate characters are
distinct. This route uses all test algebras rather than density of
field-valued points.

`coordinatePinning` completes the actual coordinate root datum to a
split pinning while retaining the actual diagonal torus and its
inclusion. Under adjacent-root numbering, induction along the
coordinate indices expresses the difference of the first diagonal
character and any other diagonal character as a nonnegative sum of
simple roots. At the induction step the next adjacent simple root is
added. Thus `inclusion_isHighestWeight` proves the complete published
highest-weight package: all-test irreducibility, full torus-weight
decomposition, a one-dimensional highest space and the weight bound.

`SpecialLinearFirstFundamentalHighestWeightStatement` and its proved
instance `specialLinearFirstFundamentalHighestWeight` quantify every
field `k : Type u` and every `n`, giving an actual reduced coordinate root
datum and pinning for `SL_{n+2}` with adjacent-root numbering and full
integral coroot span, such that the actual column representation has
first fundamental highest weight. The root datum comes from the
unconditional `exists_coordinateRootDatum`. The first-weight formula
proved in `SpecialLinearFundamentalWeights` identifies its actual
fundamental basis vector with the first diagonal character.

The diagonal character calculation and the first-diagonal-character
highest-weight lemma also cover `SL_1`; the endpoint statement uses
`SL_{n+2}` so that the first fundamental weight exists.

Provenance is internal: this is a computation from the existing actual
special-linear matrices, integral characters, separating-coefficient
lemmas and coordinate root datum. It imposes no characteristic or
perfection condition and uses no rational-point density or
representation-existence assumption. The comparison with the norm-one
Tits algebra remains a separate obligation.

The coordinate pinning uses `SpecialLinearTitsCocycle.coordinatePinning` for the same diagonal torus, root datum and base.
