# Two-point sharp-fixer factorization of an actual root point

This internal unit proves the elementary root-point case of the mixed
factorization needed for common apartments in the existing quotient.

For arbitrary apartment data `D : KPApartmentData i ω` of an actual maximal
split torus of a connected reductive group over a field, and any two apartment
points `x,y`, `exists_mixed_factorization_of_mem_rootGroup` factors every
individual `g ∈ U_a(k)` as `p * n * q`. Here `p` belongs to the actual sharp
fixer of `x`, `n` belongs to the actual normalizer, and `q` belongs to the
actual sharp fixer of `y`. The group, root subgroups, normalizer and sharp
fixers are all the published ones.

If the value of `g` at `x` is nonnegative, take `p=g` and the other factors
equal to the identity. If its value at `y` is nonnegative, take `q=g`.
In the remaining case, both values are negative and finite. Actual rank-one
factorization supplies opposite factors `r,s` with `r * g * s` in the
normalizer. V5 and its published second-factor consequence give the value
of `r` at `x` as the negative of the value of `g` there, and the value of
`s` at `y` as the negative of the value of `g` there. Thus `r` and `s`
belong to the required opposite-root depth-zero filtrations. Their
inverses belong to the sharp fixers, giving
`g = r⁻¹ * (r * g * s) * s⁻¹`.

The Prop-valued `RootPointMixedFactorizationStatement` quantifies this result
over all the stated data at arbitrary universe `u`;
`rootPointMixedFactorization` proves that exact proposition.
The provenance is internal: the proof combines the published actual
rank-one factorization, the root-valuation axioms and the inclusions of
depth-zero root filtrations in sharp fixers.

This does not establish factorization for arbitrary products of root
points, for the whole rational-point group, or the existence of common
apartments. Such a product argument requires an additional proof: the set
of mixed factorizations is not asserted to be closed under multiplication.
No bounded-subgroup fixed-point or maximal-boundedness theorem is claimed.
