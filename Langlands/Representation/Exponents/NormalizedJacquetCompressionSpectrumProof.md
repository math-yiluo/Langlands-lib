# Spectral bound for the actual normalized Jacquet compression

Author: Worker 19.

`Langlands.normalizedJacquetCompressionSpectrum` proves the complete
unapplied `NormalizedJacquetCompressionSpectrumStatement.{uG,uV}`.
The group and representation carrier universes remain independent.

The helper `jacquet_mk_ne_zero_of_compression_eigenvector` shows that a
nonzero compression eigenvector with nonzero eigenvalue survives in the
actual unnormalized Jacquet quotient. If its quotient vanished,
`Jacquet.powerKernelSup_eq_ker_of_iwahoriContraction` would place it in
the kernel of some power of compression. That power acts on the vector
by a nonzero scalar, giving a contradiction. The proof uses the actual
power-kernel supremum, without assuming a canonical lift.

The theorem `norm_normalized_compression_eigenvalue_lt_one` first handles
the zero eigenvalue directly. In the nonzero case it transports the
nonvanishing quotient class through `Jacquet.Localization.trivialEquiv`.
The published
`Jacquet.mk_compressedAction_of_iwahoriContraction` identifies the
unnormalized action on this class. The exact action formula
`Aubert.General.normalizedJacquetFunctor_obj_apply` then multiplies the
eigenvalue by `HaarModulus.closedInverseHalfCharacter`.

Admissibility of this actual normalized Jacquet module follows from
`Aubert.General.isAdmissible_normalizedJacquetFunctor_obj_of_iwahoriContraction`
and the stated contraction-basis hypothesis. Applying
`Langlands.exists_centralExponent_of_generalized_eigenvector` to its
central operator produces a full-center exponent with this normalized
eigenvalue. The displayed strict exponent hypothesis finishes the bound.

All geometric contraction conditions remain explicit hypotheses of this
internal helper. No GL-specific result, classification, geometric lemma,
adjointness, character independence, or cuspidal support theorem is used
in its argument. The helper does not discharge the geometric hypotheses
of the full rational-point criterion and does not claim any coefficient
or integrability estimate.
