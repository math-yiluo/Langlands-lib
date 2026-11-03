# Pointwise normalization from Borel conjugacy

This internal auxiliary construction restricts a normalizing base point to an
automorphism of any monic represented subgroup. It also gives a conditional
pointwise self-normalization argument for a closed subgroup containing an
ambient Borel. It does not prove `ParabolicSelfNormalizerStatement`.

The normalizer condition is the published condition on every refinement of
every test scheme. Conjugating the representing inclusion by a normalizing
base point does not change its range: the two containment directions follow
from conjugation by the point and by its inverse. The uniqueness of monic
representatives then gives `normalizerRestrictionIso`. Its inclusion equation
is the exact restriction of the ambient inner automorphism.

Conversely, a source automorphism satisfying that inclusion equation gives
normalization on all refinements, using the automorphism and its inverse.
All-test normalization in particular normalizes the ordinary point subgroup
on any fixed test scheme.

For `i : P → G`, let an ambient Borel `j : B → G` factor as `f ≫ i`. Assume
conjugacy of Borels inside `P` and equality of the abstract point normalizer
of `j(B(k))` with `j(B(k))`. A point `n` in the all-test normalizer of `P`
restricts to an automorphism `σ` of `P`. The two maps `f ≫ σ.hom` and `f`
are Borels of `P`, by the published promotion and transport lemmas.
Conjugacy gives `p ∈ P(k)` and `φ : B ≅ B` with
`(f ≫ σ.hom) ≫ Int(p) = φ.hom ≫ f`. Composing with `i`, naturality of
inner conjugation shows that `i(p) * n` normalizes `j`. The assumed Borel
normalizer equality puts this product in `j(B(k))`, hence in `i(P(k))`.
Multiplication by `i(p)⁻¹` puts `n` in `i(P(k))`.

This is derived from the existing subgroup functor, monic-representative,
Borel transport, conjugacy and inner-automorphism interfaces. The two
structural point hypotheses are explicit and remain obligations in any
application. There is no inference from pointwise equality to equality of
subgroup functors on nonreduced tests.
