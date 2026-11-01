# Second-block specialization and corank L divisibility

This internal supporting module composes actual second-block coefficient
specialization, convergent corank integrals, and the existing L-polynomial
divisibility theorem. Its field, block-carrier and second representation
universes are independent. The representations may be reducible.

`secondBlockZeroEquiv` is an equivalence from the actual lower induction at
second-block parameter zero to `TwoBlockJacquet.inducedRep F h σ`, including
their section carriers. The identity linear equivalence intertwines the
inducing actions because `twoBlockSecondDeformedBlocks_zero` identifies the
entire ordered family. Applying `Induction.smoothInducedEquiv` then produces
the required equivalence of the smooth section representations. This avoids
treating equality of inducing actions as definitional equality of their
dependent section carriers.

`secondBlockZero_isOfWhittakerType` derives full standard Whittaker type from
full standard type of both blocks. The published
`DominantRankTransport.lowerInduced_inverseWhittakerType` uses complete ordered
lower-to-upper block reversal and the full normalized upper type theorem.
The standard/inverse character equivalence and `secondBlockZeroEquiv` transport
this full predicate to the actual zero-parameter induction. No induced-type
premise is added.

`secondBlock_modelDenominatorBound_at_zero` assumes the closed
`TwoBlockSecondWhittakerDeformationStatement`, a nonzero standard functional
`J` on the zero-parameter induction, and a nonzero scaled-standard functional
on a full Whittaker-type representation of rank `r + 1`. The induced rank is
`r + 2`; the block sizes are otherwise unrestricted. It also assumes
`P₀ * P₁ ≠ 0` and, for each vector in the second functional's actual coefficient
image, `SecondBlockCorankRealRayClearing` above some real bound. That predicate
requires formal clearing of every actual deformed coefficient by the
specified spectral clearing kernel.

For each original coefficient pair, the proof first converts the
scaled-standard character to the inverse standard character using the
existing functional and coefficient adapters. It applies
`secondBlock_corankClearing_at_zero` to obtain a finite Laurent numerator for
the original coefficient series cleared by `(P₀ * P₁).toLaurent`. The
convergence theorem in `corankOneCoefficient_clearing_denominatorBound`
applies to the full types and nonzero functionals already supplied or derived.
Its conclusion bounds every rational continuation of this actual corank
integral by the Laurent span of the reciprocal product polynomial.
The supplied compatible quotient measure is preserved throughout.

`secondBlock_polynomialDivisibility_at_zero` additionally assumes a complete
`IsPadicSymmetricLPolynomial` certificate `hP` for this zero-parameter
induction and the second representation. It applies
`adjacentRankModelBound_polynomialDivisibility` to the preceding model bound,
obtaining a polynomial `Q` and natural number `e` satisfying exactly

`X ^ e * (P₀ * P₁) = Q * P`.

The arbitrary additive Haar measure is passed to the convergence and
certificate APIs. These results require neither self-duality for the
convergence step nor irreducibility, positivity of `r`, or nonzero coefficient
vectors. They do not construct the complete L certificate or certificates for
`P₀` and `P₁`. Both the deformation theorem and the real-ray formal clearing
remain explicit inputs. Neither exact adjacent-rank parent target is proved
by this module.

The provenance is internal composition of the named Lean results, with no
new direct literature assertion. The identity inducing-action construction
is adapted from Workers 831 and 15's independently reviewed second-block
deformation draft (`TwoBlockSecondDeformation.zeroComparison`); that draft's
analytic theorem is not imported or assumed to be published here.
