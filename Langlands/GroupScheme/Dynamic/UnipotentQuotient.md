# Smooth quotients on dynamic unipotent subgroups

This internal construction specializes the published positive-semigroup comparison
and smooth equivariant quotient theorem to conjugation by a cocharacter. It
works over every field at the ambient universe, with smooth affine source and
target groups. The ambient homomorphism is smooth and surjective on schemes.
Ambient connectedness is not required.

`unipotent_eq_positiveSemigroup` applies
`RelativeRoot.dynamicUnipotentSemigroupComparison` to the split torus `Gm` and
its identity cocharacter. Preservation of products and inverses proves that the
ambient homomorphism intertwines the two conjugation actions.

`exists_unipotentQuotientHom` applies `semigroupSmoothQuotient` to supplied
representatives of the two dynamic unipotent subgroup functors. It gives a
homomorphism commuting with the ambient maps, smooth and surjective on schemes.
`unipotentQuotientHom` chooses it and `unipotentQuotientHom_spec` records these
three properties. This concerns the actual group schemes and all relative
test schemes; it does not assert surjectivity on points over the ground field.

`unipotent_isFppfImage` supplies the existing actual
`SubgroupFunctor.IsFppfImage` predicate by the positive-semigroup comparison and
`isFppfImage_semigroupSubgroup`. This includes represented source and target,
a commuting homomorphism, flatness, surjectivity and local finite presentation.

The provenance is internal composition of the imported published theorems,
parallel to the existing `Dynamic.ParabolicQuotient` construction. This supplies
a factor quotient for Task 6404's kernel-cell application; it does not yet prove
kernel saturation or the depth-zero opposite-factor statement.
