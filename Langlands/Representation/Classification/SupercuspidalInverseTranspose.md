# Supercuspidality under inverse transpose

This internal transport result applies to every field `F : Type uF`, every
matrix size `n`, and every complex representation on an independent carrier
`V : Type uV`. The quotient equivalence is algebraic. The supercuspidality
theorem assumes an arbitrary topology on `F`, as does the existing definition
of admissibility, and imposes no topology on `V` and no irreducibility condition.

`BlockShape.inverseTransposeCoinvariantsEquiv` identifies the actual coinvariants
of `ρ.comp inverseTranspose` for a standard upper block radical with the
coinvariants of `ρ` for its opposite radical. It is the existing image-subgroup
coinvariant equivalence, with its target rewritten by the proved equality
that inverse transpose maps the upper radical onto the opposite one. It sends
each quotient representative to the class of the same vector.

`isSupercuspidal_comp_inverseTranspose` proves that the actual inverse-transpose
pullback is supercuspidal when `ρ` is. Admissibility follows from continuous
group-equivalence transport. The existing standard-radical criterion reduces
the remaining condition to a proper block shape `B`. Reversing its ordered
block sizes preserves properness, and conjugation by the constructed reverse
block permutation maps the reversed upper radical onto `B`'s opposite radical.
Supercuspidality of `ρ` therefore annihilates that actual opposite quotient.
The displayed linear equivalence transfers its subsingleton property to the
required quotient of the pullback.

The provenance is internal: this combines the Library's actual image-subgroup
coinvariant equivalence, its standard-radical supercuspidality criterion,
continuous inverse transpose, and the proved radical and reverse-block image
equalities. It does not use Gelfand–Kazhdan duality or a contragredient
identification. In the Godement–Jacquet functional-equation argument it supplies
the supercuspidal hypothesis needed to apply the existing nonzero-output
construction to the actual comparison representation.
