# Compact rank-one determinant-band representatives

This internal construction proves the determinant-band covering estimate in
rank one and constructs a positive form on the original rank-one finite adelic
action from a unitary central character. It works over every number field `F`
in arbitrary universe `uF`. The covering and integral estimates require only
continuity of the test function; neither cuspidality nor a central character
is needed for those estimates.

`IdeleAbsoluteValue.normSection` is a continuous positive scalar section of the
actual normalized idelic absolute value. For a positive real unit `h`, it is
the idele whose common archimedean scalar is `h^(1/[F:ℚ])` and whose finite part
is one. The existing `PrimitiveAdelicHeight.scalarRoot` construction supplies
this root. Its proved norm identity includes the field-degree normalization,
so `full_normSection` proves that the normalized absolute value of the section
is exactly `h`. Continuity follows from continuity of the positive real power
and of the actual positive scalar idele map.

`IdeleAbsoluteValue.exists_isCompact_bandCover` applies for every real lower
bound `lo>0` and every real upper bound `hi`. It uses the proved compact set `C`
of norm-one ideles meeting every principal idele coset. The set of positive
real units with real values in `[lo,hi]` is compact by
`PositiveRealTorus.isCompact_unitsBox`. Multiplication maps the product of
that box with `C` continuously to a compact idele set. For an idele `z` in
the norm band, remove the scalar section of its norm; the result has norm one.
Choose a principal multiple of that norm-one factor in `C`, then restore the
scalar section. Commutativity of ideles shows that the resulting representative
is a principal left multiple of the original `z`. No ordering relation between
`lo` and `hi` is needed: if the interval is empty the covering assertion is
vacuous.

`AdelicGL.scalar_determinant_one` proves that every actual one-by-one invertible
adelic matrix is the scalar matrix of its determinant idele, using the
one-by-one determinant formula on entries. Thus
`AdelicGL.exists_isCompact_determinantBandCover` maps the compact idele
representative set through the actual scalar matrix map. Compatibility of
scalar matrices with coefficient change turns every principal idele multiplier
into the actual rational one-by-one matrix multiplier. The resulting compact
set covers the entire closed determinant band by rational left translation.
The determinant norm is precisely `AdelicBlockDeterminantCharacter.determinantNorm`,
not a separately normalized scalar quantity.

`lintegral_enorm_sq_lt_top_of_isCompact` proves finiteness of the squared
extended-norm integral of every continuous complex function over every compact
matrix set, for any measure finite on compact sets. The proof applies the
continuous-on-compact integrability theorem to the continuous real function
`x ↦ ‖f(x)‖²`, then rewrites its finite-integral assertion using the identities
for extended norms of powers and real norms. The actual adelic matrix topology
is Hausdorff by the published homeomorphism with the group-scheme adelic points;
that proved topology fact supplies measurability of compact sets.

`exists_rankOne_cover_finite` combines these two results. For every positive
lower bound and arbitrary upper bound, one measurable compact covering set
works simultaneously for every continuous complex matrix function. The measure
may be any measure finite on compact sets, for any Borel measurable structure
compatible with the existing matrix topology. No invariance hypothesis on the
measure is needed, so the result applies in particular to the actual matrix
Haar measure.

`rankOneFiniteInvariantPositiveForm` selects that covering set at bounds one
and two for `matrixHaarMeasure F 1`. It applies the integral estimate to the
original continuous function attached to each `S.Space` vector and passes the
result to `finiteInvariantPositiveFormOfCover`. Its output is an invariant
positive definite Hermitian form on exactly `S.finiteRepresentation`, with the
original carrier and action. It retains only the common unitary continuous
idele-class central character. No cuspidality, preexisting form, square
integrability or decay hypothesis is retained. A compatible Borel structure
can always be selected for the matrix topology. The prescribed rank-one local
object then inherits this form through the separate
`CuspidalSpectralUnitaryForm` transport.

The provenance is internal: the proof composes the proved norm-one idele
compactness theorem, the positive scalar root and compact-unit-box constructions,
one-by-one matrix identities, continuous-on-compact integration and the actual
Haar pairing. It discharges the rank-one analytic case of the host task; the
higher-rank cuspidal covering estimate and the universal local-unitarity theorem
remain separate obligations.
