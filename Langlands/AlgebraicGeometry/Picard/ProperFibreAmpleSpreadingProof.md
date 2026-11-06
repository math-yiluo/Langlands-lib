# Spreading ampleness of a specified line bundle from a proper fibre

The theorem
`Langlands.AlgebraicGeometry.Picard.properFibreAmpleSpreading` proves exactly
`ProperFibreAmpleSpreadingStatement.{u}` in every universe. For a proper
morphism `f : X ⟶ S` over a locally noetherian base, a specified actual line
bundle `L` on `X`, and any point `s : S`, ampleness of its pullback to the
scheme-theoretic residue-field fibre gives an affine open neighbourhood
`V ∋ s` on whose inverse image the actual restriction of this same `L` is
ample.

The implemented proof applies
`properFibreAmpleSpreading_of_powerSectionLifting` from
`ProperFibreAmpleFromSectionLifting` to the theorem
`Modules.properFibrePowerSectionLifting` from
`Modules.ProperFibrePowerSectionLiftingProof`. The latter proves the exact
section-lifting premise: one degree threshold works for every higher power
and every fibre section, with a possibly section-dependent affine base
neighbourhood. Its proof uses the reduction to a noetherian local base,
uniform cohomology vanishing on maximal-ideal layers, and stable images of
proper cohomology, as explained in its paired Markdown.

The geometric implication chooses a finite affine generation-open cover on
the ample fibre, raises its sections to one degree above that threshold,
and lifts them simultaneously to one affine base neighbourhood. The actual
pullback and tensor-power comparisons preserve their entire generation
opens on the fibre. Proper geometric shrinking then makes the restriction
of the specified bundle ample after a further affine shrinking. The
implication returns this open in the original base.

This is an internal composition of these two published Library results.
Their paired explanations give the cohomological and geometric proofs and
their source comparisons. The lifting premise is discharged by its theorem;
the final theorem has no additional premises. The arbitrary point, all
universes and possible nilpotents are retained, with no flatness or chosen
projective embedding assumed. The original statement and imported pairs are
preserved. The finite-set affine-neighbourhood consumer remains a separate
result, and this module makes no representability claim.
