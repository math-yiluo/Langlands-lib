# Uniform products in unipotent matrix representations

This internal derived unit uses the Library's actual `IsUnipotent` predicate,
which provides a nonzero common fixed vector in each nonzero finite matrix
representation on every relative scheme test.

`MatrixRepresentation.HasUnipotentProductBound ρ d` says that every list of
at least `d` represented points, on any test scheme `T`, has zero ordered product
of the matrices `ρ(x) - 1` over `Γ(T, O_T)`. The product is ordered; commutativity
of these matrices is not assumed.

`hasUnipotentProductBound_of_isUnipotent` proves this property with `d = m`
for every representation indexed by `Fin m`, over any field and at arbitrary
universe `u`. Neither smoothness, connectedness, affineness, finite type nor
reducedness is assumed for the group or the tests.

The implemented proof inducts on `m`. In dimension zero all matrices coincide.
In positive dimension a common fixed vector is moved to the first basis vector,
using the published fixed-vector and conjugation machinery from
`Absolute.UnipotentPointsSolvable`. The existing tail representation acts on the
quotient by this fixed line. By induction a sufficiently long product of its
differences is zero. The corresponding full product has only its first row
possibly nonzero: its tail vanishes and its lower first-column entries vanish.
Multiplication on the left by one further difference kills that row because the
difference annihilates the first basis vector. Finally, conjugation of the whole
ordered product transfers the zero equation to the original representation.

`pointMatrix_sub_one_pow_eq_zero_of_isUnipotent` takes a constant list and obtains
`(ρ(x) - 1)^m = 0` on every test.

This supplies matrix product bounds only. It does not yet prove termination of
the group-scheme descending central series, existence of a nontrivial smooth
central vector subgroup, equivariant linearization, or the ordered-product
statement.
