# Smooth quotients on dynamic parabolics

This internal construction specializes the published semigroup realization,
dynamic comparison and smooth quotient theorems to conjugation by an arbitrary
cocharacter. It is a prerequisite for the split-radical pseudo-parabolic descent
proof. The construction works over every field and at the ambient universe;
source and target groups are smooth, connected and affine. The ambient
homomorphism is required to be smooth and surjective on schemes.

`parabolic_eq_nonnegativeSemigroup` applies `dynamicSemigroupComparison` to the
split torus `Gm` and its identity cocharacter. It identifies the actual dynamic
parabolic on every relative test scheme with the semigroup subgroup for the
nonnegative halfspace. The homomorphism intertwines the two conjugation actions
by preservation of products and inverses.

`exists_parabolicQuotientHom` then applies `semigroupSmoothQuotient` to any given
representatives of the two parabolics. It produces a commuting restriction
homomorphism which is smooth and surjective on schemes. `parabolicQuotientHom`
chooses this homomorphism, and `parabolicQuotientHom_spec` records its commuting
square and both geometric properties. The choice concerns a homomorphism
between supplied representatives and adds no hypothesis about local sections.

`parabolic_isFppfImage` combines the same comparison with
`isFppfImage_semigroupSubgroup`, using the proved `semigroupRealization` and
`semigroupSmoothQuotient`. Thus its conclusion is the existing actual
`SubgroupFunctor.IsFppfImage`, which includes represented source and target,
a commuting homomorphism, flatness, scheme surjectivity and local finite
presentation. It is stronger than ordinary pointwise image containment and does
not assert pointwise surjectivity on the original test scheme.

All mathematical content here is derived from the imported published theorems;
there is no additional external source assertion or unproved prerequisite.
