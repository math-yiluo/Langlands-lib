# Counting ample sections under finite flat pullback

Let `K` be algebraically closed and let `f : A.X ⟶ B.X` be a morphism over
`Spec K` between abelian schemes with `f.left` finite and flat. For an ample
line bundle `L` on `B`, `finrank_globalSections_pullback_of_finite_flat` proves
that the dimension of the complete section space of `f* L` is the dimension of
the section space of `L` multiplied by `f.left.finrank y`, the rank of the
finite flat map at any point `y` of `B`. In particular, if the dimensions of
these section spaces are equal, `isIso_of_finrank_globalSections_pullback_eq`
proves `IsIso f.left`. The morphism need not be étale, and neither theorem
requires it to be a group homomorphism.

## Implemented proof

- `eq_dimension_of_finite_flat` works over any field. The unit of `A` is a
  closed point because the section is a closed immersion; its image by the
  finite map is closed. A flat locally quasi-finite morphism preserves the
  local Krull dimension at these points, which is the relative dimension for
  each abelian scheme by `field_closedPoint_stalk_dimension`.
- `eulerCharacteristic_eq_finrank_ample` uses ample higher-cohomology vanishing
  and the isomorphism from degree-zero cohomology to relative global sections.
  `coeff_lineBundleEulerPolynomial_eq_finrank_ample` uses the square identity
  for Euler characteristics in `AmpleNonvanishingSection` and nonnegativity
  of the characteristic at exponent one to identify the coefficient at the
  dimension with the section count.
- Pullback by the finite map is ample by `affinePullbackAmple`. The published
  `finiteFlatEulerPolynomialCoefficient` for the common relative dimension
  compares the two coefficients at each `y`; transporting the structure map
  by `Over.w f` identifies the Euler characteristics on the source. Substituting
  the two section counts gives the asserted rank formula.
- The count on `B` is nonzero, by `eulerCharacteristic_ne_zero_of_isAmple` and
  cohomology vanishing. With equality of counts, cancellation gives rank one
  at each point, and `Scheme.Hom.isIso_iff_finrank_eq` gives the isomorphism.

This is an auxiliary result for the quotient-and-count argument in Mumford,
*Abelian Varieties*, §17, printed pp. 164–165 (PDF p. 87 of the registered scan
`mumford-abelian-varieties-full-scan`). It uses the actual Euler polynomial
rather than a formula for intersection numbers. It does not assert existence
of a quotient or that all sections descend to one.
