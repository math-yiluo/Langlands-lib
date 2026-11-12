# Geometry after composition of bases

Author: Worker 109.

This internal construction extends `BaseCompositionSheaf` to actual algebraic
spaces. It derives its conclusions from the original represented pullbacks,
representable diagonal, and etale atlas; no external literature assertion is
claimed as proved here.

For any schemes `S,T : Scheme.{u}` and morphism `g : S ⟶ T`,
`BaseComposition.space g X` is an algebraic space over `T`. Its underlying
sheaf is `BaseComposition.sheaf g X.toSheaf`, whose sections retain an original
structure map to `S`, an original section over that map, and its equation over
`T`. No condition on `g` is imposed. Tests are all schemes and section values
are in `Type (u+1)` at arbitrary `u`.

`schemeComparison` identifies a composed represented presheaf with the
presheaf of the same representing scheme over `T`. A section in the former
contains an original structure map and a morphism to the representing scheme;
the latter morphism determines the original structure map. Forgetting this
redundant coordinate is natural and bijective. Its inverse is `schemeIso`.
`schemeComparison_naturality` and `schemeIso_naturality` prove compatibility
with morphisms of representing schemes.

`map_isPullback` proves that the presheaf base-composition functor preserves
pullback squares. It evaluates the square on any test over `T`. Equality in
the common target first identifies the two original structure maps to `S`.
The original pointwise pullback over that structure map then gives existence
and uniqueness. This uses the actual presheaf square, with no restriction to
rational points or affine tests.

For a map `a` from a represented scheme presheaf, `fromScheme g a` uses
`schemeIso` to compose its base. `schemeIso_hom_id` and `fromScheme_section`
identify the corresponding section with `liftSection` from the original
presheaf construction.

`relative_map` takes any scheme-morphism property `P` respecting
isomorphisms and a transformation whose represented projections have `P`.
For each scheme section of its composed target, that section determines an
original structure map to `S` and an original target section. After expressing
the test scheme using that map, the corresponding natural transformation is
exactly `fromScheme` of the original one. The original represented pullback,
viewed over `T`, represents the new pullback: `map_isPullback` and the two
scheme comparisons give its square. The projection has the same underlying
scheme morphism, so it retains `P`. No base-change stability assumption on
`P` is needed. `representable_map` is the specialization to the always-true
property, and `relative_fromScheme` additionally changes the represented
source using `schemeIso`.

`hasRepresentableDiagonal_presheaf` uses Mathlib's criterion that every map
from a represented scheme be representable. Such a map to the composed
presheaf is, as above, a `fromScheme` map over its original structure map. Its
original map is representable by the original representable diagonal;
`representable_map` and `schemeIso` preserve that conclusion.

`isAlgebraicSpace_sheaf` combines this diagonal with the original atlas,
viewed over `T`. The scheme morphism properties etale and surjective respect
isomorphisms, so `relative_fromScheme` supplies both atlas properties.
`space`, `spaceMap`, and `spaceFunctor` give the actual space, natural
transformations, and functor. `spaceSchemeIso` gives the same-scheme
comparison as an isomorphism of algebraic spaces.

The relative-property transport concerns representable transformations.
This module does not yet transport general smooth or surjective space
morphisms, geometrically connected fibres, or finite type of the structural
map. It also does not prove separatedness over the new base for arbitrary
`g`. These and the arithmetic/topological assembly remain obligations for
the unchanged unconditional adelic smooth-openness target.
