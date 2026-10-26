# The open full-measure inverse-row tail locus

The proposition definition
`Langlands.GeneralLinear.PadicMirabolicTailConullStatement.{uF}` concerns
actual invertible matrices over every finite extension `F` of `Padic p`,
for every prime `p` and every supplied `T : F.TopologicalData`. The local
field topology is exactly `T.topology`; the matrix unit group uses its
induced topology and its Borel measurable space.

For arbitrary natural numbers `a,b`, set `N = a+b+1`. The proposition asserts
that the set of `g ∈ GL_N(F)` for which at least one of the last `b+1`
coordinates of the last row of `g⁻¹` is nonzero is open. Its second conclusion
is that the complementary set, on which all those coordinates vanish,
has measure zero for **every** left Haar measure on this actual group.
The Haar premise is Mathlib's `Measure.IsHaarMeasure`: left invariance,
finite mass on compact sets, and positive mass on nonempty open sets.
No normalization of the Haar measure is imposed.

The row index is `Fin.last (a+b)`. The tail indices are precisely
`Fin.natAdd a j` for `j : Fin (b+1)`. Thus the coordinates are computed
in `g⁻¹`, and the tail includes the final coordinate. The statement includes
`a=0` and `b=0`. When `a=0`, the exceptional set is empty because an
invertible matrix has a nonzero last row. When `b=0`, the statement concerns
the nonvanishing of the final entry of that inverse row.

This is a derived internal geometric prerequisite for a prospective
mirabolic restriction argument for normalized block induction. Its provenance
is the explicit inverse-row coordinate condition on the existing
`GeneralLinear` construction, rather than a transcription of a literature
theorem. A possible proof separates the exceptional set into finitely many
pieces with a nonzero head coordinate and applies elementary unipotent left
translations and Steinhaus's theorem. Regularity of Haar measures and the
existence of nonzero field parameters in every neighborhood of zero must be
derived in the supplied topology in that proof.

This module defines a proposition and supplies no proof. It constructs no
parabolic or mirabolic intersection and does not identify this locus with
any product or orbit. It makes no assertion about quotient measures,
induced representations, Hilbert completions, Mackey theory, or
irreducibility.
