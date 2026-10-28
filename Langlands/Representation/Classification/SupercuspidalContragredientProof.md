# Supercuspidality and the smooth contragredient

Author: Worker 115. Worker 196 identified the published natural Jacquet
duality interface used to discharge the remaining vanishing step.

`Langlands.GeneralLinear.supercuspidalContragredient` proves exactly
`Langlands.GeneralLinear.SupercuspidalContragredientStatement.{uF,uV}`.
For every smooth complex representation of the actual `GL_n(F)`, it proves
that its smooth contragredient is supercuspidal if and only if the original
representation is supercuspidal. For admissible representations it also
proves equivalence of irreducibility. Field and carrier universes remain
independent, every rank including zero is covered, and every block shape
is retained. The target and its imported Lean/Markdown pairs are unchanged.

## Provenance

This proof is an internal derivation from published constructions and
theorems. The target's source explanation records Casselman's smooth
contragredient, admissibility, irreducibility and cuspidality conventions.
The present proof uses the proved natural upper/opposite Jacquet equivalence
from `Langlands.Representation.Parabolic.NaturalJacquetDualityProof`,
smooth admissible duality from
`Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof`,
the reversed-block geometry of `Langlands.Group.GL.ReverseBlocks`, and the
transfer lemmas in
`Langlands.Representation.Classification.SupercuspidalContragredientAux`.
It does not require characterization by a supplied asymptotic pairing.
That separate stronger statement is not proved here.

## Jacquet vanishing and preservation

The public helper
`GeneralLinear.jacquet_vanishing_smoothContragredient_of_opposite` assumes
an admissible representation and a subsingleton actual opposite Jacquet
quotient. `Parabolic.standardNaturalJacquetDuality` supplies a representation
equivalence from the normalized upper Jacquet module of the smooth dual to
the smooth dual of the normalized opposite Jacquet module of the original
representation. The latter carrier is subsingleton because its source
carrier is subsingleton. Injectivity of the equivalence makes the upper
Jacquet module subsingleton. The inverse of `B.jacquetModuleEquiv` transfers
this conclusion to the actual ambient upper coinvariant quotient. This
explicitly keeps the internal-radical upper quotient distinct from the
ambient quotient. Normalization changes the actions, not these carriers.
No smooth separation or admissibility theorem for a Jacquet module is used.

`GeneralLinear.isSupercuspidal_smoothContragredient` first applies the
published standard-block criterion. For a proper shape `B`, the upper
quotient for `B.reverse` vanishes, since
`B.reverse_parabolic_ne_top_iff` preserves properness. The actual action
of `B.reverseMatrix` induces the published conjugate-coinvariant
equivalence, and `B.reverse_unipotentSubgroup_map_conj` identifies its target
radical with the opposite radical of `B`. The preceding helper now proves
upper vanishing for the smooth dual at `B`. This works uniformly in every
rank and shape. Compact open subgroups chosen by
`T.generalLinearCompactOpen` form a cofinal family inside the open
subgroups, as supplied by the existing `GeneralLinear.compactOpen_cofinal`
in `Representation.Category.Contragredient`, so the published smooth admissible-duality theorem also gives
admissibility of the smooth dual. The standard-block criterion finishes
preservation, including vanishing for all conjugates.

## Reflection and irreducibility

For reflection, admissibility of the smooth dual first gives admissibility
of the original smooth representation through
`isAdmissible_of_smoothContragredient`. Preservation applied to the dual
then proves supercuspidality of the smooth bidual. The published admissible
duality theorem makes the actual canonical evaluation `smoothBidual`
bijective. Its representation equivalence transports supercuspidality
back to the original representation.

For the irreducibility equivalence, smooth admissible duality supplies
smooth separation for every smooth representation in the carrier universe,
including invariant quotients, and canonical bidual bijectivity for the
given admissible representation. The published auxiliary theorem
`isIrreducible_smoothContragredient_iff_of_bidual` applies these facts.
Its invariant-annihilator argument reflects irreducibility; applying
reflection again to the dual and transporting through canonical biduality
proves the converse. The admissibility reflection and irreducibility
transfer helpers remain publicly available from the imported auxiliary
module; this module exposes the new Jacquet vanishing and supercuspidality
preservation helpers.
