# The actual general-linear Haar pairing

This internal construction discharges the support and right-invariance premises
of the determinant-band pairing using the actual general-linear rational
quotient Haar measure. It applies over every number field `F`, with arbitrary
field universe, to the unchanged operator realization `S` of rank `n`.

`haar_isMulRightInvariant` proves right invariance of the fixed ambient Haar
measure on the actual adelic group-scheme points. The helper module
`GroupScheme.Lie.GeneralLinearAdjointDeterminant` proves that the actual
rational character `det Ad` of GL over a characteristic-zero field is zero;
its paired Markdown explains the scalar-action and character-classification
argument. The Library theorem
`PlaceGroupPoints.localModularCharacterAdjointDeterminant` identifies every
local analytic modular character with the normalized absolute value of this
same algebraic character. The proved local-to-adelic assembly
`modularCharacter_eq_characterNorm_of_local` gives the corresponding equality
on the full adelic group. Finally,
`haarRightInvariant_of_adjointDeterminant_eq_zero` sets that character to zero
and uses the right-translation formula for the actual Haar measure. The affine
and smooth GL instances are proved Library instances installed locally; no
supplied reductivity, determinant-triviality or analytic comparison premise is
retained. This argument applies to every rank, including zero.

`measurePreserving_translate` installs that ambient right invariance and
applies the existing descent theorem for the principal rational quotient.
It proves that every positive right translation `[x] ↦ [x g]`, expressed
through the original adelic matrix homeomorphism, preserves exactly
`quotientHaarMeasure F n`. No determinant-norm restriction is needed for this
full quotient result. A norm-one translation therefore also preserves the
restriction to the strict determinant band `(1,2)` by the existing geometry.
The full-support instance for this measure is the one proved in
`OperatorDeterminantSliceMeasure`.

`finiteInvariantPositiveFormOfHaar` specializes the existing
`finiteInvariantPositiveForm` with this measure, its full support and the
proved right invariance. Its result is an invariant positive definite complex
Hermitian form on exactly `S.finiteRepresentation`, with the original carrier
and action. It retains positive rank, a common unitary continuous idele-class
central character, and square integrability of every original quotient function
on the determinant band. The central character and positive rank supply the
faithfulness and normalized-translation arguments in the existing pairing;
this module does not assume a positive form on the original space.

`finiteInvariantPositiveFormOfCover` replaces that band square-integrability
premise with an explicit measurable matrix set `t` and two hypotheses: every
matrix with real determinant norm in the closed interval `[1,2]` has a rational
left translate in `t`, and the squared extended norm of each original realized
function has finite integral over `t` with respect to `matrixHaarMeasure`.
That ambient matrix measure is the pushforward of the same fixed Haar measure
used above, so there is no change of normalization. The existing
`memLp_band_of_cover` proves the required band square integrability for each
vector, and `finiteInvariantPositiveFormOfHaar` then constructs the form.
The matrix Borel measurable structure can be any one compatible with its
existing topology.

The provenance is internal: this is a specialization and composition of proved
Library Lie, character, modular-character, quotient-measure and pairing
results. Neither constructor derives its remaining integrability hypothesis
from cuspidality. This unit therefore does not prove
`CuspidalUnitaryLocalUnitarityStatement`; the cuspidal covering estimate and the
transport to the prescribed original local component remain separate work.
Positive rank includes rank one, and no presentation universe is specialized
by this intermediate finite-action construction.
