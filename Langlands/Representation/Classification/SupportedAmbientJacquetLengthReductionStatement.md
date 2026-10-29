# Supported ambient Jacquet length reduction

`Langlands.GLSupportedAmbientJacquetLengthReductionStatement.{uF,uV,uW}`
is an internal derived proposition. It isolates the finite-series obligation for
a specified quotient of refined cuspidal induction. This file states the
reduction; it does not prove it.

For every supplied p-adic field and compatible topological data, and every
positive rank `n`, the premise is the exact published proposition
`CuspidalSupport.CuspidalInductionLengthTheorem.{uF,uV} F T n`.
For an actual block shape `B` and refinement `S`, the fine datum `ω` is
irreducible and cuspidal on the actual flattened Levi. The real fine vector
`v₀` is arbitrary. The coarse representation `π` is admissible and comes with
an actual surjective intertwiner from the fine induction at coarse parameter
zero.

For every real coarse vector `t`, let `τ` be the existing `fineTwist` and let
`πt` be the actual real determinant twist of `π`. The conclusion asserts finite
group-algebra length of the actual outer normalized induction of `πt`, finite
group-algebra length of its actual `ambientJacquet`, and a natural number `M`
such that `HasJordanHolderMultiplicity (ambientJacquet T B S πt) τ M`.
That predicate includes an actual finite composition series with simple factors
and exactly `M` factors equivalent to `τ`. No positivity of `M` is asserted.
The field, fine carrier and coarse carrier universes are independent; the outer
induction and ambient Jacquet carriers lie in `max uF uW`.

The provenance is the composition of existing Library interfaces: real-twist
transport of the support quotient, preservation of fine irreducibility and
cuspidality, `CuspidalSupport.normalizedParabolicInduced_refined_finiteLength`,
surjectivity of normalized induction maps, finite length under surjective
intertwiners, opposite Jacquet finite length for admissible finitely generated
representations, the flattened opposite Jacquet comparison, and construction of
actual series from finite length. These interfaces motivate the conditional
statement; their composition still requires a separate proof.

The standard cuspidal induction length premise remains open independently.
There is no coarse irreducibility, unitarity, temperedness, ordering, supplied
ambient series or head premise. This reduction alone proves neither the
supported all-regular comparison nor its irreducible-head conclusion.
