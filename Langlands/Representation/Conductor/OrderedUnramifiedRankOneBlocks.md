# Rank-one blocks for ordered unramified principal series

This internal helper realizes the scalar inducing characters of
`Conductor.UnramifiedPrincipalSeries` as actual irreducible supercuspidal
representations over every nonarchimedean local field, with no characteristic
restriction. The carrier of `rankOneBlock hϖ w` is `ULift.{uF} ℂ`. Its action is
multiplication by `character hϖ w (det g)`.

The construction follows the published character-line model in
`FiniteRepresentation.characterLine` and the rank-one construction in
`Correspondence/RankOneExistence`, with the latter's p-adic restriction removed
from this elementary construction. Smoothness follows from the open kernel of
the actual unramified character and continuity of the determinant.
Irreducibility is the published irreducibility theorem for character lines.
Admissibility follows from finite dimension. Supercuspidality is immediate
because a block shape of total rank one has no proper block parabolic; the
implemented proof uses `BlockShape.length_le` directly.

`fieldData` packages the ambient instances for the all-field induction and
twist API. The `Langlands.AllFieldBZ` imports are published Library modules over
`LocalFieldPackage`. Its `ofField` construction preserves the supplied field,
and `LocalFieldData.ofInstances` preserves the supplied topology and valuation.
The argument therefore applies in every characteristic.

The internal lemmas `rankOneBlock_class_ne_twist` and
`rankOneBlock_twist_ne` establish the non-twist hypothesis of
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), Theorem 4.11, for these rank-one factors. The second lemma states the
inequality in the sigma-indexed family of supercuspidal classes used by that
theorem's Library interface. Their only parameter condition is
`‖(w : ℂ)‖ ≤ ‖(w' : ℂ)‖`; equality and repeated parameters are allowed.

The implemented proof is an elementary scalar-character argument. Equality of
supercuspidal classes supplies a categorical isomorphism. Forgetting to smooth
representations gives a linear equivalence of the two actual lifted lines.
Intertwining at the scalar matrix with entry `ϖ`, and cancelling the nonzero
image of the vector `ULift.up 1`, forces
`(w' : ℂ) = (fieldData.normalizedAbs (ϖ : F) : ℂ) * (w : ℂ)`.
The lemma `normalizedAbs_uniformizer_lt_one` transports the defining valuation
inequality for `ϖ` through the canonical ordered value-group isomorphism and
uses the order comparison for the residue-normalized absolute value. Taking
complex norms therefore gives `‖(w' : ℂ)‖ < ‖(w : ℂ)‖`, a contradiction.
No residue-cardinality witness is needed for this argument.

These are derived helpers for the ordered Whittaker realization proof. This
module does not itself prove the realization statement, nor does it assert
Bernstein–Zelevinsky's nondegeneracy theorem.
