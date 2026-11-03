# Cocharacters presenting rational parabolic functors

Author: Worker 1307. Worker 1298 proposed the separation of the geometric
representability adapter from the generic-minimality reduction.

This is an internal construction and collection of logical adapters between
the published `ParabolicDynamicStatement`, the actual affine dynamic
representative, and `IsParabolicFunctor`. Every structural conclusion in this
module takes `hPD : ParabolicDynamicStatement.{u}` explicitly. The module
does not prove that statement or generic minimality.

For any field `k : Type u`, connected reductive group scheme `G` over `k`,
and cocharacter `χ : 𝔾_m ⟶ G`, the published
`Dynamic.Affine.parabolicHom χ` is a closed subgroup representing
`Dynamic.parabolic χ` on every test scheme.
`Dynamic.Affine.isParabolicSubgroup_parabolicHom_of_parabolicDynamic`
applies the reverse implication of `hPD` to this representative. Thus it
is geometrically parabolic under precisely that input.
`isParabolicFunctor_dynamic_of_parabolicDynamic` packages this actual
representative and its all-test range equality into `IsParabolicFunctor`.
Affineness is obtained from connected reductivity.

Conversely, `IsParabolicFunctor.exists_dynamicCocharacter` extracts the
geometric representative from the functor predicate and applies the forward
implication of `hPD`. The data-valued construction
`IsParabolicFunctor.dynamicCocharacter` chooses such a cocharacter over `k`.
Its specification identifies the dynamic functor with the original functor
on every scheme over `k`. The choice is not asserted to be unique or
canonical. The corresponding `iff` records the two directions.

The final two lemmas express minimality by quantifying over smaller dynamic
parabolics. In the forward direction each dynamic parabolic is parabolic
by the affine representative argument. In the reverse direction the chosen
cocharacter presents each smaller parabolic functor, so the asserted
dynamic equality gives the required equality of functors. This does not
replace all-test inclusion with a condition on rational points.

Provenance: the construction is derived solely from the definitions and
theorems in `Absolute/BorelStatement`, `Dynamic/AffineRepresentability`,
and `Rational/MinimalParabolic`. No new assertion from the literature is
introduced. The geometric structural theorem remains an assumption rather
than an available proof.
