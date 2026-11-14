# Rank-one multiplication in the sharp chamber normalizer cover

The internal set `sharpChamberNormalizerCover C` consists of actual rational
points of the form `p n q`, with both `p` and `q` in the sharp fixer of `C`
and `n` in the actual normalizer. Basic lemmas give membership of normalizer
points and stability under multiplication on either side by the sharp fixer.

The principal rank-one lemma treats `r u m`, where `r` acts as the reflection
in a simple wall `psi`, its Weyl action negates the wall derivative `a`,
`u` belongs to the wall root group, and `m` is any normalizer point. It assumes
connected reductivity, maximal splitness and AS4, with no local-field condition
or simply connected comparison.

Transport `psi` by `m` inverse and test its sign on `C`. If positive, conjugate
`u` to the right-hand sharp fixer. If negative and `u` belongs to the strict
wall filtration, reflection sends it into the strict opposite filtration,
which is the opposite root's fixer on `C`. This gives a left sharp factor.
In the remaining case `u` has exactly the affine value `psi` at every apartment
point. Actual rank-one factorization supplies an opposite factor pair
`p = (p1, p2)` and `n_u = p1 u p2` in the normalizer. V5 puts both opposite
factors in the weak opposite wall filtration. The identity

`r u m = (r p1⁻¹ r⁻¹) (r n_u m) (m⁻¹ p2⁻¹ m)`

has the required factors: the first lies in the positive wall group on `C`,
and the last lies in a positive transported affine-root group on `C`.

This is an internal consequence of published actual root factorization, V5,
normalizer covariance, chamber sign dichotomy and simple-wall filtration
lemmas. It proves the stated rank-one multiplication, not a full-group covering.
