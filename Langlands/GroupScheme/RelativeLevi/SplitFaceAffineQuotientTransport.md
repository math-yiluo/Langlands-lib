# Original coefficient quotients under actual ambient transport

This derived adapter retains the original face-term quotient after coefficient
extension and an actual ambient group isomorphism. The source ring is
nontrivial. The coefficient algebra is arbitrary, including the zero ring.
The finite exact-layer index types are kept separately. Their cardinalities
agree by the unchanged root datum and exact face heights; both may vanish.

Starting from an original split face chart with its reductive ambient group,
maximal torus, full root datum and genuine root parametrizations, the construction
chooses a face chart on the actual coefficient-changed roots. It then compares
that chart with any independent face chart on the roots transported through
the specified ambient isomorphism. Both retain the original root datum and
presenting weight. Equality with the original face functional proves exact
equality of their unscaled face heights; no target-ring nontriviality is needed.

`affineTransportTermIso` is the composite of actual coefficient term comparison
and actual torus-compatible root transport. Its ambient equation retains the
original pulled-back inclusion followed by the specified ambient isomorphism.
The comparison preserves consecutive step maps.
`affineTransportQuotientIso` retains the full original coefficient quotient,
with its standard vector coefficient isomorphism, and its factorization theorem
commutes with precisely this actual term comparison and the fresh quotient map.

Both quotient comparisons have a derived positive common scalar weight.
Arbitrary-ring scalar rigidity therefore makes each commute with every natural
scalar power. Their composite has weight one on the actual original map.
The identity root-datum transport has its actual coordinate-torus square proved
in the implementation. Neither term equivariance nor quotient linearity is
assumed. The result supplies the original-to-transported-fresh comparison used
for overlaps of affine parabolic face charts in the relative-radical filtration
construction; it does not assert global descent or the final filtration theorem.
