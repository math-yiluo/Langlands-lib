# Continuation of the strict-rank L bound to zero

This internal unit proves the complete symmetric L-polynomial bound for the
actual lower two-block induction at the original, undeformed parameter when
`t < r`. The field, test carrier and dependent block carriers retain independent
universes `uF`, `uV` and `uW`. The character is the supplied nontrivial unitary
additive character, and its supplied self-dual Haar measure is preserved.
All representation hypotheses are full Whittaker type, including reducible
representations; no induced type or factor existence is assumed.

## Actual coefficient analysis

`strictRankCoefficient_continuationData` supplies both a rational continuation
and an absolute bilateral spectral expansion for the same actual unequal-rank
integral and its literal `strictSliceCoefficient`. It first uses the published
strict continuation and analytic wrappers. Genuine unequal-rank convergence
then gives summability of the absolute spectral terms and the integral's sum
through `unequalRankSliceExpansion_of_converges`. `strictIntegral_eq` identifies
the Borel rectangle presentation with the original supplied product-Haar
integral. The quotient measure must be compatible, its unipotent Haar is right
invariant, and both fixed functionals are nonzero.

`strictRankCoefficient_clearing_of_certificate` starts from a complete symmetric
L certificate for a polynomial `P` and an ordinary polynomial equation
`X^e * A = Q * P`, with `A` nonzero. The certificate specializes at the supplied
compatible quotient measure and complementary rows to its intrinsic normalized
generator. The equation places `1/P` in the Laurent span of `1/A`. Actual
unequal-rank analysis puts the integral's rational continuation in that span.
Writing its Laurent numerator and using scalar spectral uniqueness then proves
finite clearing of the literal coefficient series by `A.toLaurent`. This is not
cancellation of a polynomial on arbitrary bilateral series.

## Opposite real twists

`StrictOppositeRealRayClearing` asserts finite clearing at every complementary
rectangular row, for every coefficient in each nonzero-functional model of the
actual complex opposite-twist lower induction, at all real parameters above one
bound. Its kernel uses fixed original block polynomials with substitutions
`X -> spectralPoint(q,-u) * X` and `X -> spectralPoint(q,u) * X`.

`exists_strictOppositeRealRayClearing` obtains the real-twist symmetric L bound
from `exists_strictTwoBlockSymmetricLBound`. Its conditional analytic input is
discharged by the published exact closed theorem
`twoBlockDominantFirstBlockLaurentIdentity`, imported from
`TwoBlockDominantFirstBlockLaurentIdentityProof`. Full unramified-twist
L-polynomial transport and uniqueness identify the retained block polynomials
with the fixed original polynomials under these two substitutions. Their
constant coefficients are one, so the clearing polynomial is nonzero. The
coefficient-clearing lemma then applies to every displayed test and row.

## Specialization to the original pair

`strictTwoBlockSymmetricLBound_at_zero` assumes only full type of the test and
each block in addition to strict rank and the supplied field/character/Haar
data. It derives full type of the actual lower induction using complete
ordered-block reversal and normalized induction, then obtains the whole-pair
and two block L polynomials by published symmetric existence. It chooses the
canonical compatible quotient measure and nonzero fixed functionals.

For each coefficient in the original induced model,
`exists_oppositeWhittakerFamily` supplies an actual family with a common open
right level, entire point values and the prescribed value at zero. The staged
`strictSlices_entire` theorem proves entire dependence of its literal slice
coefficients. Real-ray clearing holds for the family's actual coefficients by
the preceding result. `oppositeSpectralKernel_laurent_clearing_at_zero` continues
the finite-clearing assertion to zero.

Finally, at row `j = 0`, `k = r - t - 1`, the complete whole-pair L certificate
supplies the intrinsic normalized generator. Applying
`strictCoefficient_polynomialDivisibility` to all-model finite clearing gives
exactly `X^e * (P₀ * P₁) = Q * P`. The conclusion retains all three complete
symmetric L certificates and the ordinary polynomial witnesses. The actual
lower-to-upper normalized representation transport is performed separately in
the final exact target module.

## Provenance

The unit is an internal composition of published or separately reviewed
analytic, first-block, unramified transport, entire-slice, finite-specialization
and intrinsic-generator results. It introduces no source translation and uses
neither unrestricted multiplicativity nor any later result depending on the
analytic bases. The closed first-block theorem discharges the formerly explicit
analytic proposition; its definition alone is never treated as evidence.

## All-field port

The declarations of this module that involve the p-adic field and that the Library's proofs of JPSS (3.1) multiplicativity use are re-declared over every nonarchimedean local field, of any characteristic, in `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictLContinuation` (the Markdown there lists them). For those declarations this p-adic module is superseded by the all-field port; its Lean code is unchanged.
