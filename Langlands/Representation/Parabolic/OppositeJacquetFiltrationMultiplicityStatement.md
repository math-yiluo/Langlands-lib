# Multiplicities across normalized opposite Jacquet filtrations

`Langlands.Parabolic.NormalizedOppositeJacquetFiltrationMultiplicityStatement`
states two finite-filtration multiplicity criteria. This file contains
proposition definitions, not proofs.

For a p-adic field `F`, compatible topological data `T`, a block shape `B`,
and a refinement `S`, take any smooth complex representation `ρ` of the
product Levi `B.Levi F.Carrier`. Let `s` be any supplied finite invariant
filtration of `ρ`, of length `l`. For any complex representation `τ` of
the actual group `refinedLevi F.Carrier B S` and any natural number `m`,
the refined clause states the equivalence between:

* an actual finite composition series of
  `T.normalizedRefinedOppositeJacquet B S ρ` with exactly `m` factors
  representation-equivalent to `τ`;
* natural numbers `counts i`, for every original index `i : Fin l`,
  together with an actual finite composition series of
  `T.normalizedRefinedOppositeJacquet B S (s.gradedRepresentation i).ρ`
  having exactly `counts i` such factors, and
  `∑ i, counts i = m`.

The composed clause says the same for any smooth representation of
`GeneralLinear n F.Carrier`, using
`T.normalizedComposedOppositeJacquet B S` on the representation and on
every original graded quotient. The target group is again the actual
refined Levi.

`HasJordanHolderMultiplicity` includes existence of a finite composition
series with simple graded factors. Thus the forward implication constructs
finite series for all the normalized graded quotients, and the reverse
implication constructs a finite series for the normalized whole
representation. The statement does not compare two counts while assuming
that their series exist. It imposes no simplicity condition on `τ`;
the count is still the number of simple factors equivalent to `τ`.

The intended intermediate filtrations are the fixed actual quotient-image
filtrations in `OppositeJacquetFiltration`. Each keeps every original index
and takes the image of the original invariant subspace under the actual
Jacquet quotient map. The statement allows repeated steps and zero
graded quotients; their Jacquet modules must have the finite-series
witnesses asserted in the equivalence. There is no positive-rank or
positive-length restriction. For `l = 0`, the asserted sum is the empty
sum, equal to zero.

The functors are precisely those in `OppositeRefinementFunctors`:
the inverse half of the opposite full modulus is the positive half of
the upper full modulus. The composed normalization retains both the
outer and inner factors. No change of action or refined subgroup is
part of this statement. The field, input carrier, and constituent
carrier have independent universes `uF`, `uV`, and `uW`.

This is an internal algebraic interface derived from smooth ordinary
coinvariant exactness, the fixed image-filtration graded comparisons,
and general Jordan–Hölder additivity, decomposition and transport.
A separate proof must apply these results to construct the asserted
series in both directions. No separate literature theorem is claimed.
Smoothness is the only representation hypothesis: admissibility,
irreducibility, finite length, a splitting, or an exactness or comparison
certificate is not supplied as a premise.

This statement is a prerequisite for constituentwise summation. It
does not compare inner and ambient multiplicities for a constituent,
compute a Weyl total, identify positive multiplicity with being a
quotient, or establish an irreducible head.
