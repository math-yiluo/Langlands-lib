# Positive forms on the prescribed cuspidal spectral components

This internal construction transports a positive form on the original finite
adelic action of a cuspidal realization to each prescribed local component of
each supplied spectral presentation. It works at independent field and
presentation universes `uF` and `uQ`. The conclusion concerns the original
embedded local form-space carrier and action, including its canonical p-adic
packaging.

`CuspidalOperatorRealization.FiniteSlice.unitaryForm` starts with a form on
`T.realization.finiteRepresentation`. The existing genuine equivalence
`T.realization.finiteEquiv` identifies the original operator-space carrier with
its finite image in automorphic forms. Pulling the form through the inverse
equivalence gives a form on that finite image. The faithful intertwiner
`A.inclusion` then restricts it to the actual finite slice `A.subspace`.
`unitaryForm_inner` records the exact two pullback maps in the resulting inner
product. Positivity and definiteness follow from the proved injectivity of the
inclusion and the genuine equivalence; the finite action is unchanged.

For a supplied `P : CuspidalSpectralPresentation.{uF,uQ} T`,
`localUnitaryForm` uses `P.finiteSlice.unitaryForm` and the existing
`FiniteTensorPresentation.sliceUnitaryForm`. It chooses precisely
`P.presentation.chosenTail P.finiteSlice.nonzero v`, the complementary vector
already used to define `P.localComponent v`. Consequently its result is a form
on that same embedded component, not merely an isomorphic factor or a different
slice. The existing slice inclusion is injective and intertwines the original
one-place local action, so the pulled-back Hermitian form is definite and
invariant. No factorization of the global inner product is assumed.

`padicUnitaryForm` packages this identical form on exactly
`((P.localComponent v).padicObject hI hA).obj.representation`. The existing
`padicObject` keeps the original carrier and action definitionally. Its
irreducibility and admissibility inputs are the same proofs `hI` and `hA`
used by the target statement. The result installs
`(padicField v).canonicalTopologicalData.topology`, as in the target;
no alternative topology or representation is selected. The form itself is an
algebraic positive definite invariant Hermitian form and requires no topology
on its carrier.

`padicUnitaryFormOfHaar` obtains the original finite-action form from
`OperatorDeterminantSlice.finiteInvariantPositiveFormOfHaar` and then applies
this transport. It retains a common unitary continuous idele-class central
character and square integrability of every original realized function for the
actual rational quotient Haar measure restricted to the strict determinant
band `(1,2)`. Positive rank is `r+1`, so the existing rank premise is discharged
by `Nat.succ_ne_zero`; this includes rank one. Full support and right invariance
of the actual quotient measure are already proved in the imported measure and
Haar modules.

`padicUnitaryFormOfCover` instead applies the corresponding original
finite-action covering-set constructor. It retains a measurable set of original
adelic matrices, rational left covering of every matrix with real determinant
norm in the closed interval `[1,2]`, and finiteness of each original function's
squared extended-norm integral over that set. The matrix Haar measure is the
pushforward of the same actual ambient Haar measure used to construct the
quotient measure. Any Borel measurable structure compatible with the original
adelic matrix topology is allowed. The constructor returns the form on the
exact prescribed p-adic object, with the same quantifiers over presentations,
places, irreducibility and admissibility witnesses.

The provenance is internal: the new definitions compose the existing faithful
finite-image equivalence, finite-slice inclusion, chosen tensor-slice form and
canonical local packaging. The last two constructors also use the previously
constructed actual Haar pairings. No positive form is assumed in those last
two constructors, but their explicit integrability hypotheses remain to be
derived from cuspidality. This unit therefore does not prove the unconditional
`CuspidalUnitaryLocalUnitarityStatement`. Once the actual cuspidal covering
estimate is supplied as a proved theorem, its hypotheses fit
`padicUnitaryFormOfCover` directly. No relation between `uF` and `uQ` and no
replacement of the original component carrier is used.
