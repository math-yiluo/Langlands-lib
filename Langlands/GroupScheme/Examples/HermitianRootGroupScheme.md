# The actual group scheme of a nondegenerate diagonal Hermitian form

This internal construction takes fields `k` and `L` in an arbitrary common
universe, with a specified separable quadratic extension `L/k`. The finite
middle index `Middle` is a type in the lowest universe, as required by the existing
special-linear Weil-restriction model. The data are a diagonal Hermitian
form `H` over `L`, fixed by the canonical quadratic conjugation, and actual
units `w i` whose values are its middle weights. No anisotropy or
characteristic restriction is imposed.

The actual ambient group is the affine Weil restriction of the
special-linear group indexed by `Unit ⊕ (Middle ⊕ Unit)`. For every actual test
scheme over `Spec k`, `tensorForm` extends the original middle weights
along the inclusion of `L` into the tensor product with the test scheme's
relative global-section algebra. The involution on this coefficient ring
and its naturality under test restrictions are the existing SU3 tensor
constructions. Conjugation of a pure tensor proves that the included
weights are fixed. `tensorUnits` maps the supplied units into the same
coefficient ring. Every actual test restriction preserves these weights.

The homomorphism `twistPoints` transports the weighted inverse-adjoint
endomorphism through the existing ambient tensor-matrix equivalence.
Its matrix formula is `J⁻¹ * bar(g⁻¹)ᵀ * J`, with the genuine invertible
weighted Gram element. Coefficient naturality gives naturality on all
test schemes, so `homOfPoints` constructs the actual group-scheme
endomorphism `twist`. Its matrix action is proved explicitly.

The functor `fixedFunctor` is its actual fixed subgroup functor. The
construction `groupScheme` equips the actual scheme equalizer of `twist`
and identity with its represented group structure. The actual inclusion
is exactly the equalizer inclusion. Since the affine ambient group scheme
is separated, this inclusion is a closed immersion; the equalizer group
scheme is therefore affine.

The multiplicative equivalence `fixedPointsEquiv` identifies scheme
equalizer points with the fixed subgroup functor. `fixedTensorEquiv`
then identifies them with the actual fixed special-linear tensor
matrices. Composing with the earlier exact fixed-point/isometry
comparison gives `pointsEquiv`: on every test scheme, points are exactly
the invertible matrices of determinant one preserving the full weighted
Hermitian Gram matrix. `pointsEquiv_val` shows that the underlying matrix
is the actual ambient-inclusion matrix. `pointsEquiv_naturality` and
`pointsEquiv_map` prove that actual test restrictions act entry by entry
through the specified tensor coefficient map, also as an equality in
the actual isometry subgroup.

The provenance is internal: tensor extension of the given weights,
the existing affine Weil restriction and its actual point equivalence,
the weighted matrix inverse-adjoint calculation, and scheme equalizers.
This provides an actual affine group scheme and all-test point
comparison. Smoothness, reductivity, rational-point evaluation,
generation, comparison with rational parabolic radicals and the
unrestricted local Kneser–Tits theorem remain separate obligations.
