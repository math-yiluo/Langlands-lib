# Descent data induced on an actual fppf quotient

Let `p : S → B` be a morphism of schemes in universe `u`, let `D` and `E` be
actual Cech descent data on group schemes `G` and `N` over `S`, and let
`i : N → G` respect those data. Suppose `q : G → Q` is a supplied quasi-compact
fppf quotient whose full scheme-kernel range is the all-test range of `i`.
`Descent.quotientDatum D E i q hi hq` constructs an actual Cech datum on `Q`,
and `compatible_quotientDatum` proves that `q` respects it. No field, smoothness,
reducedness or affineness premise is imposed here. The conclusion is a descent
datum, before its effectiveness is used.

This construction is derived from `FppfQuotientComparison`, the Library's fpqc
homomorphism descent, and the actual Cech data and direct-pullback comparison
equations in `Descent.Data`. It assumes an existing quotient and does not prove
general normal-subgroup quotient existence.

`FppfQuotientDiagram.map` first handles a commuting square of actual subgroup
inclusions `i ≫ a = b ≫ i'` with supplied quotients on both sides. The square
carries every point of the first full kernel into the second full kernel.
Thus `a ≫ q'` kills that kernel. Fpqc homomorphism descent gives the actual map
of quotients, and `map_fac` proves its defining factor equation. If both `a`
and `b` are isomorphisms and both quotient maps are quasi-compact, applying
this construction to the inverse square gives the inverse quotient map.
`FppfQuotientDiagram.iso` is the resulting actual isomorphism.

The two pullbacks of `q` to the double overlap remain fppf quotients by the two
pullbacks of `i`. Compatibility of `i` with `D` and `E` is exactly the square
needed to construct `quotientOverlap`. Its factor equation says that composing
the first quotient with this overlap isomorphism equals the ambient overlap
isomorphism followed by the second quotient.

`pullHom_quotientOverlap_fac` pulls that equation to any refinement, retaining
the direct-pullback comparisons. On the triple overlap, the two possible
composites agree after precomposition with the base-changed quotient from the
first ambient group. This quotient is flat and surjective, so it detects
equality of maps. The ambient datum's cocycle therefore proves
`quotientOverlap_cocycle`. These actual isomorphisms and this equation form the
constructed quotient datum.
