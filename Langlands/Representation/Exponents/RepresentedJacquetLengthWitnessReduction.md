# From an actual detecting Jacquet family to length two

This internal reduction implements the length-counting step suggested by
Renard VI.5.4, printed p.174 / PDF p.180 of the registered 2026 edition
`renard-2026-representations-groupes-reductifs-padiques`. It uses the Library's
proved finite-family length theorem to avoid a finite-length assumption on the
source. It does not prove existence of the witness defined in the companion
module.

## Exactness with an explicit compact-limit radical

`leviJacquetFunctor_mapsShortExactIntertwiners` proves exactness on every short
exact sequence for the actual represented normalized Jacquet functor, with
values in the Levi's own rational point group. It assumes that the actual
radical point image is a limit of compact subgroups.

The implemented proof supplies the represented semidirect decomposition and
closed radical to
`Langlands.Aubert.General.jacquetFunctor_map_isShortExact`, which already proves
exactness of normalized Jacquet restriction from the character-localization
exactness theorem. Pullback along `leviPointsEquiv` changes the acting group and
retains the underlying linear maps. Consequently the resulting injectivity,
range-kernel equality and surjectivity are definitionally the required claims.
The proof reorders the conjunctions from `SmoothRep.IsShortExact` into
`Derivative.Mirabolic.MapsShortExactIntertwiners`.

## Counting lengths without assuming finite length

`repLength_le_of_hasRepresentedJacquetLengthWitness` unpacks a witness, equips
each target Levi point group with its own canonical topology and forms the
actual family of normalized Jacquet functors. The preceding exactness lemma
supplies exactness for each member.

It applies the published `Langlands.exactFamilyLengthBound` to the witness's
individual image-length bounds and detection of every irreducible actual
subquotient. That theorem constructs a finite composition series of length
`m ≤ ∑ i, b i`, without assuming source finite length. The implemented proof
uses `repLength_eq_of_hasSimpleFactors` to identify actual composition length
with `m`, then combines this inequality with the witness's total budget. The
field universe `u` and source carrier universe `w` remain independent.

## Application to maximal-Levi induction

`maximalLeviSupercuspidalLengthBound_of_jacquetLengthWitness` instantiates the
preceding theorem on actual normalized induction. Its sole unresolved input is
`MaximalLeviSupercuspidalJacquetLengthWitnessStatement.{u,v}`, and it proves
`MaximalLeviSupercuspidalInductionLengthBoundStatement.{u,v}`.

`maximalLeviSupercuspidalLengthTwo_of_jacquetLengthWitness` composes that
implication with the represented endpoint-extraction theorem
`maximalLeviSupercuspidalLengthTwo_of_lengthBound`. Thus a witness also yields
actual irreducible subrepresentation and quotient endpoints in a short exact
sequence whenever the induction is reducible.

These are conditional implications. Construction of the represented family,
the budget-two image bounds and detection remain unresolved, as do the
exponent and unitarity steps of the final VII.1.3 target. No target or imported
Lean/Markdown pair is changed by this module.
