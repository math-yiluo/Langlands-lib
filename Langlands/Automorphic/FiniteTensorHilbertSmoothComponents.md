# Smooth representation objects of actual completed tensor slices

Author: Worker 2.

This internal construction bundles the intrinsic smooth part of an actual
completed tensor slice as a smooth representation, proves its admissibility
and irreducibility under the specified original-factor hypotheses, and compares
its genuine isomorphism class with the existing algebraic form slice.

## Actual objects and hypotheses

The number field has universe `uF`; the family of original local carriers has
the independent universe `uV`. Scalars are complex, matrix rank is any natural
number, and the groups and their topologies are the actual finite-completion
matrix groups. The construction retains a supplied `FiniteTensorPresentation P`
of the given local representation family and a supplied invariant positive form
`b` on its actual global realization `S.representation`.

`sliceHilbertSmoothRange b v y` is the published intersection of the actual
completed invariant slice with the smooth subrepresentation of the original
global completed action restricted along local insertion. Its carrier and
action come from that global completion. No topology is imposed on the
original algebraic factor.

## Smooth object and intrinsic properties

The generic `TensorSmoothRangeAux.isSmooth_of_le_smoothSubrepresentation`
proves that every subrepresentation contained in an ambient smooth
subrepresentation is smooth. For each subtype vector it takes the ambient
open subgroup fixing that vector; subtype extensionality proves the same
fixed-vector equation for the inherited action.

`sliceHilbertSmoothRange_isSmooth` applies this result to the intersection's
containment in the ambient smooth vectors. It requires neither a nonzero
complementary tensor nor admissibility. `sliceHilbertSmoothRepresentation`
bundles precisely that carrier and action as a `SmoothRep`, and
`sliceHilbertSmoothClass` takes its existing quotient by actual categorical
isomorphism. Both use the actual completion's carrier universe `uF`; the
original factor's potentially different universe is not resized or identified
with it. Zero slices are allowed for these definitions.

For an explicit nonzero complementary tensor and `IsAdmissible (ρ v)`,
`sliceHilbertSmoothRange_isAdmissible` transports admissibility along the
published `factorHilbertSmoothEquiv`. This preserves the existing convention
of finite generation of fixed spaces for all open subgroups. With the further
algebraic irreducibility input, `sliceHilbertSmoothRange_isIrreducible`
transports irreducibility along the same equivalence using the published
`LengthTwo.isIrreducible_of_equiv`. No closed-subspace condition substitutes for
this algebraic conclusion.

## Comparison with algebraic slices and change of choices

`sliceToHilbertSmoothEquiv` composes the inverse of the published algebraic
`sliceEquiv` with `factorHilbertSmoothEquiv`. Its source is the existing actual
form slice, and its target is the intrinsic smooth Hilbert slice. The theorem
`sliceHilbertSmoothClass_eq_slice` passes its inverse to `SmoothRep.mkIso` and
the existing quotient equality criterion. It identifies the two actual smooth
classes without comparing class labels from different carrier universes.

`sliceHilbertSmoothChangeEquiv` compares two genuine presentations of the same
local representation family, exceptional set, reference vectors and reference
invariance data. The global realization, supplied positive form and nonzero
complementary tensor may differ. The map first inverts the first original-factor
equivalence and then applies the second. Its target and source are the two
actual intrinsic smooth slices, and its intermediate representation is the
same original local factor. `sliceHilbertSmoothClass_eq` applies `mkIso` and
the quotient equality criterion to this actual equivalence. It proves class
independence within those fixed tensor data.

## Provenance and limits

This is an internal derivation from the published smooth-range and smooth
equivalence constructions, algebraic tensor-slice equivalences, smooth
representation category, and admissibility and irreducibility transport APIs.
The elementary smoothness proof and the composed actual equivalences are
explained above. No original-literature identification is asserted.

The class comparisons require admissibility and explicit nonzero tails; the
irreducibility result also requires irreducibility of the specified factor.
No existence of a tensor presentation or invariant positive form, canonical
normalization, unitarity of the comparisons, equality of embedded subspaces,
automorphic occurrence or global spectral decomposition is asserted.
