# The actual conjugate as a presented cuspidal contragredient

Worker 837. Internal comparison helpers for Task 6821.

For a cuspidal realization with unitary central character, the Library provides a
positive invariant unitary form and joint admissibility. The latter follows from
the proved adelic `GL_n` Siegel finiteness theorem. The published criterion
`OperatorRealization.isContragredientOf_of_unitaryForm` applies to the actual
antilinear conjugation map, which commutes with the finite, compact and real Lie
actions. Thus the pointwise-conjugate realization is a full-operator
contragredient of the original.

The published `cuspidalDualPresentationExistence` supplies a spectral presentation
of this specified conjugate realization, in the same factor universe as a
supplied presentation of the original. Both universe parameters are retained.
`PresentedConjugateContragredientStatement` records these two consequences, and
`presentedConjugateContragredient` proves it.

For a presentation of a second supplied contragredient, both spectra are the
inverse multiset of the original spectrum by
`CuspidalOperatorRealization.eigenvalues_eq_map_inv_of_isContragredientOf`.
Consequently the conjugate presentation and the supplied contragredient
presentation have equal spectra at places where all three presentations are
unramified. Substitution in the definition of `partialEulerFactor` gives equality
of their pair Euler factors.

These are derived comparisons between already constructed actual realizations.
Their provenance is the Library's unitary-conjugate criterion and dual
presentation existence, with the unitary-form and admissibility route explained
in the imported paired documentation. No new classification or continuation
result is assumed.
