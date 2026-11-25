# Relative quasi-affineness descends along a flat quasi-compact surjection

`Langlands.AlgebraicGeometry.relativeQuasiAffineFlatDescent.{u}` proves
`Langlands.AlgebraicGeometry.RelativeQuasiAffineFlatDescentStatement.{u}`
for schemes in any universe `u`. If `p : S' ⟶ S` is flat, quasi-compact
and surjective, quasi-affineness of `X ×_S S' ⟶ S'` implies
quasi-affineness of `f : X ⟶ S`. This is the descent implication of
Stacks Project, Descent, Lemma 35.23.22 for the singleton fpqc cover
given by `p`. See PDF p. 58 of the registered edition
`stacks-descent-ed88ff78-2026` (SHA-256
`28e718bac216bb7c4584e9edb1d25d6420ee19a6cd536742c58599242ff8cad4`).
[Stacks Project, Tag 02L7](https://stacks.math.columbia.edu/tag/02L7)

Fix an affine open `V` in the target of `f`. Quasi-compactness of `p`
makes the inverse image of `V` quasi-compact, since the restriction of
`p` to `V` is quasi-compact and `V` is affine. Take the finite subcover
of the affine cover of that inverse image. Composing its open immersions
with the restriction of `p` gives flat maps `q i` to `V`. These are jointly
surjective because the affine opens cover the inverse image and the
restriction of `p` is surjective.

Each affine chart also maps by an open immersion `b` into `S'`.
`isQuasiAffine_pullback_affine_open` applies the hypothesis for the base
change along `p` to this chart and gives quasi-affineness of the pullback
of `f` along `b ≫ p`. The restriction identity gives
`q i ≫ V.ι = b ≫ p`. Pasting the pullback square for `f ∣_ V` with the
pullback along `q i` thus identifies the two pullback schemes.
`Scheme.IsQuasiAffine.of_isAffineHom` transports quasi-affineness along
the resulting isomorphism. The finite affine-family descent theorem
gives quasi-affineness of the inverse image of `V` under `f`.
[Affine-open pullback helper](QuasiAffineEtaleDescent.md),
[finite affine-family descent](QuasiAffineCoverDescent.md)
