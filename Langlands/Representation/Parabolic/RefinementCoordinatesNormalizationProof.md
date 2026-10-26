# Ordered refinement normalization and induced functions

`Langlands.Parabolic.refinementCoordinatesNormalization` proves the exact
`RefinementCoordinatesNormalizationTheorem` for the published coordinate inputs.
It proves the full positive modulus identity, agreement of the specified
canonical positive halves on the Levi and parabolic, and an equivariant linear
equivalence of the actual smooth induced representations preserving every
underlying ambient function in both directions.

The coordinate hypothesis first identifies the original ordered shape with
`D.flatten S`. The label equivalence has the same finite cardinality as the
canonical flattened block equivalence. The published consequences of the exact
coordinate identity show that an earlier outer block has earlier fine labels,
and that the fine labels within an outer block are strictly increasing. Thus,
viewed through the canonical flattened numbering and the block-count cast, the
given labels define a strictly increasing endomorphism of a finite ordinal.
Such an endomorphism fixes every element. The block labels therefore agree,
and the supplied size equalities identify the size functions. Equality of the
block-shape structures follows; their positivity and total-rank fields are
propositions.

After this shape equality, `nestedLeviEquiv_apply` and
`flattenedLeviProductEquiv_apply` identify the concrete Levi equivalence with
`flattenedLeviEquiv`. The two formulas use the same matrix reindexing; equality
proofs used for the size casts do not change it. The proof then applies
`PadicField.TopologicalData.composedLeviModulus_flattened` from
`Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation`.
This imports the full determinant-product calculation and introduces no supplied
modulus premise. `modulus_of_coordinates` exposes this full-character clause
for the same arbitrary coordinates.

`halfModulus_of_modulus` applies the canonical nonnegative square root and
complex embedding to the full modulus equality. Equality of units follows from
equality of their values. The parabolic clause follows from the published
`composedLeviProjection_parabolicRefinementEquiv` compatibility. These are the
specified positive halves, with no choice of a square root.

`induction_of_halfModulus` uses the published
`Induction.conjugateSmoothInducedEquiv` at the identity conjugator, with the
concrete parabolic refinement equivalence. The coordinate map preserves the
ambient matrix. The inducing actions agree because the parabolic halves agree,
the Levi projections correspond, and inverse Levi coordinates cancel forward
coordinates. The inverse of the generic equivalence has the direction from
composed induction to ordinary induction. Its two evaluation formulas reduce to
identity maps on the ambient functions. The generic construction preserves the
same uniform open right stabilizer and intertwines right translation. No
smoothness premise on the original representation is used.

This is an internal derivation from the published coordinate, character and
induction constructions. The raw flattened calculation is imported rather than
repeated. The theorem retains arbitrary rank, including zero, empty block
families and independent field and value universes. It asserts no interpretation
of the determinant character as Haar scaling.
