# Sign of the actual semistandard Plancherel density

`rationalSemistandardDensitySign` proves
`RationalSemistandardDensitySignStatement`: the scalar
`GlobalForm.componentDensity` is a nonnegative real number at every point
of every unitary twist orbit of the intrinsic semistandard spectrum, and
its real part is strictly positive on a dense subset of each orbit. The
field universe `u` and the representation-carrier universe `uV` stay
independent, and the density may vanish at individual points.

For one orbit, with Levi model `m`, cocharacter presentation `r`, split
component `a`, quotient Haar measure `mu` and packet data `q`, the
private theorem `orbitDensity_sign` proves both assertions for
`SourceForm.orbitDensity`, which is the density `componentDensity` at
that orbit. The main theorem applies it to the orbit representative of
each index.

1. `CocharacterPresentation.leviNormalization` transports the
   square-integrable representation and the given quotient Haar measure
   to the dynamic Levi of `r`. Its split-center field identifies the
   transported central subgroup with the point image of a split component
   of the parameter scheme. `finite_dynamicSplitQuotient`, from
   `DynamicOrbitDensityFromOppositeContinuations`, then makes the
   quotient of the dynamic Levi by the common norm kernel and this
   subgroup finite.
2. `conditionalDynamicOppositeUnitaryScalar` applies to the two
   continuations, their open convergence subsets and the open
   irreducibility locus in `q`, together with the transported
   representation and measure. It gives that the opposite-intertwiner
   composition scalar `j_P` is nonzero and that its inverse has a
   nonnegative real value at every unitary unramified character of the
   dynamic Levi.
3. Nonnegativity on the orbit is
   `orbitPlancherelWeight_nonneg_of_forall` applied to these values, with
   the unitary regularity `q.inverseRegular` from the packet data.
4. For dense positivity, `rankOneGammaProduct_ne_top_of_isSplitTorus`
   uses the maximal split torus to make the rank-one gamma product
   finite. `dense_plancherelWeight_pos` then gives a dense set of unitary
   characters of the dynamic Levi at which the Plancherel weight, the
   inverse scalar times the product of the squares of the gamma constants,
   is a positive real number.
5. Restriction along the Levi model isomorphism, `characterRestrict`, is
   a homeomorphism between the unitary unramified character groups of
   `levi p` and of the dynamic Levi; its inverse restricts along the
   inverse isomorphism and composes with the point homeomorphism of the
   model. The preimage of the dense set under this homeomorphism is
   dense. The orbit map `discreteSeriesOrbitMap` is an open quotient map
   (`isOpenQuotientMap_discreteSeriesOrbitMap`), so a subset of the orbit
   is dense when its preimage is. The identity
   `orbitPlancherelWeight_orbitMap` writes the density at the twist of the
   base point by `z` as the Plancherel weight at `characterRestrict m r z`,
   which places that preimage inside the preimage of the positivity set.

The sign assertions are those of Waldspurger (2003), Lemma V.2.1, printed
pp. 292–293, and the nonvanishing of the opposite scalar is IV.3(6),
p. 287. The proof above follows the Library's dynamic Levi formalization
of these steps.
[DOI 10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
