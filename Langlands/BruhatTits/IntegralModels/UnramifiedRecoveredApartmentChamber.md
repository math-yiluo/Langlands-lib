# Ordinary stable chambers from recovered apartment models

This is a derived internal construction. It combines
`UnramifiedRecoveredRootRestriction`, `ReductiveQuotientExistence` and
`UnramifiedIncidentRootChamber`; it makes no independent claim about an
external source.

The supplied apartment `D`, its full integer-valued compatibility with the
centralizer `C`, and the actual prescribed torus map `f : S ⟶ T` are retained.
Here `S` is maximal split over the nonarchimedean local field `F`, and `T`
becomes maximal split over `inertiaFixedField F`. Connected reductivity of the
ambient group and the equality `groupHom f ≫ iT = iS` are explicit hypotheses.
The universe `u` is arbitrary, with no restriction on either characteristic.

The input `M : RecoveredApartmentFixerModels D Ω` supplies the actual lower
and upper component models and their full and neutral recovery isomorphisms.
The subset `Ω` is arbitrary. The additional equality `hN` identifies the
*entire* upper neutral integral-point subgroup with the intersection of
`E.zeroPoints` and the pointwise fixer of the singleton apartment point `p`.
This equality is an additional input, rather than a consequence of the fields
of `M`. The proposition `UnramifiedRootPositiveReductionStatement` is another
explicit input. No reductive quotient is required as supplied data.

`hasIncidentGaloisDirections_of_recoveredModels` first chooses a valid
reductive quotient of the actual lower neutral special fibre using
`SpecialFibreQuotientData.exists_isReductiveQuotient`. The lower residue field
is finite, hence perfect. For each relative root occurring as the derivative
of an ordinary affine root vanishing at `p`,
`incident_root_restrict_ne_zero` proves that its composition with the
coefficient pullback of the specified `f` is nonzero. The incident-root
direction adapter then gives a direction fixed by every coefficient
automorphism on which that ordinary affine derivative is nonzero.
This theorem does not assume that `p` itself is fixed.

`exists_regular_galois_stable_facet_of_recoveredModels` additionally takes
coefficient stability of `D` and fixedness of `p` under its actual affine
coefficient action. Connected reductivity ascends to the algebraic upper
field. The same-apartment fixed-direction criterion produces a point regular
for `D.affineRoots`, and every actual affine coefficient automorphism
preserves its entire sign facet setwise. The apartment in the conclusion is
the original supplied `D`. Ordinary affine roots, rather than extended
affine roots, define both regularity and the facet.

`recoveredApartmentChamberPoint` chooses such a point, retaining regularity and
whole-facet invariance in its subtype. The choice is not asserted to be
canonical.

This conditional unit does not prove
`UnramifiedSpecialApartmentChamberStatement`. In particular it does not
construct the recovered models or the zero datum, prove the global neutral
equality or positive reduction, or provide the initial fixed point from those
inputs. It does remove the separately supplied quotient and incident-root
nonvanishing premises from the conditional chamber construction.
