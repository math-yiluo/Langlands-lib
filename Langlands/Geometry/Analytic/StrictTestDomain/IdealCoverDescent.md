# Ideals on strict rational covering families

This internal module supplies a strict rational-family interface for the
remaining Laurent and standard-cover ideal-descent proofs. Its propositions
are definitions, not axioms or proofs of effectiveness.

`CompatibleIdealSections` records equality of closed extensions on each
actual ordered-pair rational intersection. `idealSectionContraction` is
the explicit intersection of inverse images in the original strict base
algebra. `IdealCoverSeparated` expresses locality of global ideal membership,
and `IdealCoverDescent` expresses effectiveness of compatible ideal families.

`compatible_ideals_apply` proves equality of extended compatible ideals
after any pair of bounded maps to a common presented strict affinoid, provided
their composites from the original base agree. The rational representation
universal property factors these maps through the actual intersection;
composition of closed ideal extension proves the equality. This also proves
compatibility of global extensions and of local families transported along
the actual rational coefficient comparison maps.

For a finite rational point cover over a complete nontrivially normed
ultrametric field, `idealCoverSeparated_of_covers` proves global ideal
membership locality. Quotient the strict base by the given ideal, which is
closed by the existing strict ideal-closedness theorem. Pull the entire
rational cover back to this actual quotient. The coefficient comparison
annihilates the closed extension of the original ideal: its kernel is closed,
and the bounded structural square annihilates each original ideal element.
Scalar separation on the quotient's rational cover then detects that the
original element vanishes in the quotient. This is precisely membership in
the original ideal.

`IdealCoverSeparated.eq_of_extensions` consequently detects equality of
global ideals from equality of all closed local extensions.

The proofs are derived from the Library's strict rational representation,
actual coefficient base change, strict closed quotients, scalar rational
descent and elementary closed ideal extension. They use no ideal
effectiveness theorem and do not prove `IdealCoverDescent` in this module.
The locality theorem keeps nonreduced and zero algebras, empty spectra, and
empty finite covers. Its nontrivial coefficient-valuation hypothesis is
explicit; the separate scalar-normalization task retains the original
general-field scope.
