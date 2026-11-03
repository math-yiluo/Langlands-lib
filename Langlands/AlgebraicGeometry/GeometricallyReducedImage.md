# Geometric reducedness of a schematically dominant image

This internal geometry module supplies a descent step for represented subgroup
products. It does not assert representability or local factorization of a product.

The construction `globalSectionsEmbedding` is the pullback map on global
functions along an epimorphism, equipped with its injectivity proof. Its
underlying function is the usual `appTop` ring map.

An epimorphism of schemes whose target is affine is schematically dominant:
epimorphy makes the map on global functions injective, and an affine scheme's
kernel ideal sheaf is determined by that ring map. The proof uses the published
`Langlands.Scheme.UnitCocycleDescent.appTop_injective_of_epi` and Mathlib's
`AlgebraicGeometry.Scheme.ker_of_isAffine`.

If a quasi-compact schematically dominant map `m : X → Y` lies over a field and
`X` is geometrically reduced, then `Y` is geometrically reduced. For every field
extension test `Spec K → Spec k`, the corresponding map into `Y_K` is a flat
base change of `m` and is still quasi-compact and schematically dominant. The
source is the base change of `X`, by pullback pasting, and is reduced. Mathlib's
`IsSchemeTheoreticallyDominant.isReduced` descends reducedness to `Y_K`.

For maps between affine schemes, quasi-compactness is automatic. The final
lemma combines the two preceding facts to descend geometric reducedness from
the source of an epimorphism. These are derived scheme-theoretic arguments;
their provenance is the cited published function-descent lemma and Mathlib's
kernel, flat base change and reducedness results.
