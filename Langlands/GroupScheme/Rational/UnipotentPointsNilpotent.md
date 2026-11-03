# Uniform nilpotence of unipotent groups of points

This is an internal derivation from `Rational.UnipotentProductBound`, the
published faithful affine linear embedding, and Mathlib's abstract group lower
central series. It uses the Library's actual `IsUnipotent` predicate and actual
matrix representations. All field statements hold at arbitrary universe `u`.

`HasUniformNilpotentPoints G d` means that the `d`th lower central subgroup of
`(T ⟶ G.X)` is trivial for every relative scheme test `T`. A single `d` works
for every test, including nonreduced tests. Mathlib indexes the lower central
series with term zero equal to the whole group.

The implemented algebra argument works for any group homomorphism `f : H →* Aˣ`
into the units of an associative algebra over a commutative ring `S`; the algebra
need not be commutative. `UnitDifference.productSpan S f r` is the `S`-span of
ordered products of at least `r` differences `f(x)-1`.

- Concatenating words proves that multiplying spans adds the lower length bounds.
  The spans decrease as their length bounds increase.
- Multiplication on either side by any `f(x)` preserves each span, by writing
  `f(x) = (f(x)-1)+1`.
- `congruenceSubgroup S f r` consists of the points whose difference lies in
  the `r`th span. The product and inverse identities prove subgroup closure.
- If `x` lies in this subgroup, its commutator with an arbitrary `y` lies in
  the next subgroup. The difference of that commutator factors as
  `((f(x)-1)(f(y)-1)-(f(y)-1)(f(x)-1)) f(x⁻¹) f(y⁻¹)`.
- Induction places the `r`th lower central subgroup in congruence level `r+1`.
  A zero bound on all words of length at least `m` makes the `m`th span zero;
  decreasing the filtration then places lower central term `m` in `ker f`.

For an `m`-dimensional matrix representation of a unipotent group scheme,
`lowerCentralSeries_le_ker_of_isUnipotent` applies this argument over
`Γ(T, O_T)`, using the all-test word bound from `UnipotentProductBound`.
`hasUniformNilpotentPoints_of_mono` concludes `HasUniformNilpotentPoints G m`
when the representation morphism is monic. This bound is sufficient for
termination; no claim of a sharp nilpotency class is made.

`exists_hasUniformNilpotentPoints_of_isUnipotent` assumes only that `G` is affine,
locally of finite type over a field, and unipotent. It chooses the published
closed faithful finite-dimensional representation once, before introducing the
test scheme, so its dimension gives a bound uniform over all tests. Smoothness,
connectedness, algebraic closedness and perfectness are not premises.
`isNilpotent_points_of_isUnipotent` converts this to Mathlib's
`Group.IsNilpotent` for each group of points.

The conclusions concern the abstract groups of all-test points and a bound
uniform across them. This module does not yet construct or represent the
scheme-theoretic descending central series, prove a positive-dimensional smooth
central subgroup exists, produce a central vector group, or linearize a torus
action. Those remain obligations for `CentralStableVectorSubgroupStatement`
and the ordered semigroup-product theorem.
