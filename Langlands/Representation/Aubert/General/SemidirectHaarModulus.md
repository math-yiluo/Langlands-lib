# Haar measure in continuous semidirect coordinates

This internal construction starts from an actual semidirect decomposition
`P = M U` and continuity of its canonical projection to `M`. It is derived
directly from the published projection laws in `Parabolic`; it makes no new
representation-theoretic assertion.

The map `(m,u) ↦ m u` is a homeomorphism from `M × U` to `P`. Its inverse is
`p ↦ (projection p, (projection p)⁻¹ p)`. The inverse identities use the
projection on each factor, and continuity follows from continuity of the
projection and the topological group operations.

In these coordinates left multiplication by `p` has the form
`(m,u) ↦ (projection p * m, c(p,m) * u)`. The radical element `c(p,m)` is the
second coordinate of `p * (m,1)` and depends continuously on `m`. Thus a product
of left Haar measures on `M` and `U` is preserved by coordinate left translation:
the base and every fiber are left translations. The implementation applies
Mathlib's measure-preserving skew-product lemma. Finiteness on compact sets and
positivity on open sets transport through the homeomorphism, so the resulting
measure on `P` is left Haar.

For continuous group automorphisms `a`, `aM`, and `aU` on the three groups,
assume that `a(m u) = aM(m) aU(u)`. Then `haarChar_eq_mul` proves
`mulEquivHaarChar a = mulEquivHaarChar aM * mulEquivHaarChar aU`. Here the
character is the positive scalar `c` such that `c • map a μ = μ`, in Mathlib's
convention. The proof takes the canonical Haar measure on each factor. The
product-map identity for measures and the two factor scaling identities give
the product scalar on `M × U`. The coordinate homeomorphism transports this
identity to `P`, where uniqueness of the Haar scaling scalar identifies it
with `mulEquivHaarChar a`.

The measure results require second countability of the ambient group.
`measurePreserving_coordinates_left_mul` and `coordinates_isHaarMeasure`
assume `SFinite` for the two supplied measures. The scaling theorem assumes
local compactness of `M`, `U`, and `P`; second countability passes to each
subgroup, yielding sigma-finiteness of its canonical Haar measure and
regularity of the Haar measure transported to `P`. No separation hypothesis
or group isomorphism between the product and `P` is added.

This is an internal measure-theoretic construction from the existing
semidirect projection laws and Mathlib's Haar, product-measure, and
skew-product APIs. No external literature claim is introduced. Applying the
formula to the actual rational unipotent radicals, identifying their
normalizing automorphisms, and constructing normalized induction comparisons
remain separate obligations.
