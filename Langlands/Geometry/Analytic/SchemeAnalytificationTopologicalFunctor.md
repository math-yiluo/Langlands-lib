# Underlying topological analytification of schemes

`topologicalAnalytification K` sends a scheme locally of finite type over
`Spec K` to its glued analytification in `TopCat`. An arrow over `Spec K`
acts by the continuous map `MorphismExistence.analytification` from the
local affine charts. The source is a full subcategory of `Over (Spec K)`.
The field and schemes share universe `u`. The field is complete, ultrametric
and nontrivially normed.

The identity satisfies the local affine formula by
`isAnalytificationMap_id`. Composition satisfies it by
`MorphismExistence.isAnalytificationMap_comp`. Uniqueness of the continuous
map satisfying the formula gives the two functor laws.
`analytificationCenterNatTrans K` has the continuous center maps as components.
Its naturality is the center equation of `MorphismCompatibility.compatibility`.
The construction uses the topology of the glued spaces and continuous maps.

The functor packages the underlying topological part of Berkovich,
*Spectral Theory and Analytic Geometry over Non-Archimedean Fields* (1990),
§3.4, Theorem 3.4.1 and proof steps (2)–(3), printed pp. 63–64 (PDF pp. 77–78).
The original characterizes analytifications by representability and glues
along affine opens. Identity, composition and naturality of the centers in
that formulation follow from the universal property. Here the corresponding
local affine equations are already proved in the Library.
Literature ID `provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA-256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
