# Analytification maps of separated schemes

The localized analytic object is the existing glued atlas of the affine
opens. A morphism over the ground field acts on a pair of affine opens
with the source mapping into the target by the induced algebra map on
coordinates. The affine opens subordinate to target opens cover the source.
For separated schemes their affine intersections are affine, and the actual
coordinate maps commute with restriction to these intersections. The
localized domain gluing construction gives the analytic map of the entire
space and its formula on each chart.

This implements the gluing step of Berkovich, *Spectral Theory and Analytic
Geometry over Non-Archimedean Fields* (1990), §3.4, Theorem 3.4.1, proof steps
(2)–(3), printed pp. 63–64 (PDF pp. 77–78), in the existing localized atlas
category. Literature ID
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA-256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
The common field and scheme universe is arbitrary. The ground field is
complete, ultrametric and nontrivially normed.

`localizedAnalytification` bundles these objects and arrows for the full
subcategory of separated schemes locally of finite type over `Spec K`.
The identity is checked on the affine opens. For composition, use the
cover indexed by triples of affine opens in the source, intermediate and
target schemes such that each map sends the preceding open into the next.
On this cover the composition formula is the equality of affine maps
induced by the composite coordinate homomorphism. Equality on the cover
then gives equality in the localized analytic category.

`localizedAnalytificationTopologicalIso` has identity components on the
underlying glued spaces. The localized affine-chart formula identifies the
underlying point maps by uniqueness in `IsAnalytificationMap`.
