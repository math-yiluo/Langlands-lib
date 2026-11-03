# Algebra of actual augmentation-weight support

This is derived support infrastructure for the actual coordinate construction in
`CoordinateAction` and the exact targets in `CoordinateSemigroupStatement`.
Its source motivation is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second
edition (2015), §3.3, printed pp.107–108 / PDF pp.133–134, especially the
nonzero-product argument preceding Example 3.3.2. The formal argument below uses
the existing definitions directly.

`mul_mem_weightSpace` evaluates a product over each commutative coefficient
algebra at each actual point. Addition of characters evaluates as multiplication
of units, giving the positive pullback convention with no inverse character.
`add_mem_support` also uses that a product of two nonzero coordinates is nonzero;
its `NoZeroDivisors` hypothesis is explicit. `supportSemigroup` bundles precisely
the original raw support, without inserting zero. It can be empty.

`cotangentSupport_subset_support` takes explicit same-character surjectivity of
the augmentation quotient and lifts a nonzero class. A lift cannot be zero.
`closure_cotangentSupport_subset_support` combines this inclusion with the
nonzero-product argument by the universal property of additive semigroup closure.
These lemmas do not establish same-character surjectivity or domain geometry.

`support_subset_iff_of_eq_closure` deduces the containment criterion for every
additive subsemigroup, including the empty one, directly from semigroup closure.
`augmentationLieContainment_of_semigroup` and
`coordinateSemigroupComparison_of_semigroup` apply this to the published exact
statements. They are conditional reductions; the augmentation/Lie semigroup
equality itself still needs its geometric and filtration proof.
