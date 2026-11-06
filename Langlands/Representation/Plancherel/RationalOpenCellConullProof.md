# Haar conullness of the actual rational dynamic open cell

Author: Worker 135.

The theorem `Langlands.Plancherel.rationalDynamicOpenCellConull` proves the
unchanged `Langlands.Plancherel.RationalDynamicOpenCellConullStatement.{u}`.
It assembles the actual-point density, geometric boundary and Noetherian
measure arguments.

The helper `noetherian_and_integral` uses local finite type over a field to
obtain local Noetherianity and affineness to obtain compactness of the underlying
scheme. The existing smooth connected scheme argument in
`CharacterLatticeProof.isIntegral_of_smooth` gives integrality.

The helper `leftTranslationHomeomorph` takes the scheme isomorphism given by left
multiplication by the actual rational point. The existing composition identity
for this translation proves `evaluation_mul`, so evaluation is equivariant for
the original rational-point group law.

The helper `interior_evaluation_preimage_eq_empty` uses local Zariski density
of every nonempty analytic open subset. If a proper closed set had an inverse
image with nonempty interior, the evaluation image of that interior would be
dense and contained in that closed set. Closedness would force the closed set
to be the whole underlying scheme.

The final theorem installs the canonical rational-point topology, its Borel
measurable space and the supplied Haar measure. Actual rational points form
a Hausdorff locally compact topological group, and the imported actual Haar
regularity theorem supplies inner regularity. The geometric boundary theorem
identifies the complement of the required map `(p,v) ↦ p*v⁻¹` with the inverse
image of a proper Zariski-closed subset. The imported Noetherian nullness
theorem applies to evaluation, the underlying scheme and its left translations,
and gives the asserted zero measure.

The argument is an internal derivation from the named published targets and
their proofs. It preserves the arbitrary field universe, the actual group
scheme, dynamic subgroup carriers, canonical point topology and supplied Haar
measure. It requires no splitting, matrix realization or integration formula.
