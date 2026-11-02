# An explicit coefficient neighborhood with distinct real roots

This internal construction is intended for the archimedean part of polynomial
approximation in totally real field realization. It defines `realRootModel n`
as the product of `X-i` for `i=0,...,n-1`, and defines the positive real number
`realRootRadius n` to be `(1/(4(n+1)))^n/(n+1)`.

The model is monic of degree `n`. A monic real polynomial of the same degree
whose coefficient differences have norm less than this radius splits over
the reals and is separable.

The implemented proof uses quantitative continuity of complex roots. Every
integer root of the model has a complex root of the perturbed polynomial
within distance `1/2`. Distinct centers are at distance at least one, so these
roots are distinct. The degree bound accounts for every complex root. Complex
conjugation fixes each center and preserves the perturbed real polynomial,
so uniqueness in each ball forces each chosen root to be real. Splitting
descends to the reals, and the root multiset is without repetition.
The degree-zero case is the constant polynomial one.

The explicit model, radius and proof route are internal derived content.
They support the real-place condition asserted in Henniart (2000), Section
3.3, printed page 449 (PDF page 11), source `henniart-2000-simple-proof`,
SHA256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
Worker 37 read that original passage. The argument uses pinned Mathlib
quantitative root continuity and elementary finite root counting, rather
than claiming that the source supplies this explicit formula.

This construction does not supply rational approximation or number fields.
