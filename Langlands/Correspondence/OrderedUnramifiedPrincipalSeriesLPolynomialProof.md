# The L-polynomial of an ordered unramified principal series against trivial GL1

Authors: Worker 1789 and Worker 1738.

`Langlands.Correspondence.orderedUnramifiedPrincipalSeriesLPolynomial` proves
the unchanged published
[`OrderedUnramifiedPrincipalSeriesLPolynomialStatement.{uF} F`](SphericalStandardLPrerequisites.md)
for every p-adic field `F` and with no further hypotheses. Let `ψ` be a
nontrivial additive character and `ν` a Haar measure self-dual for `ψ`. Let
`z : Fin (r + 1) → ℂˣ` have weakly increasing absolute values. Every supplied
`IsPadicSymmetricLPolynomial` certificate `P` of
`Unramified.principalSeriesOfTuple F z` against the trivial character of
`GL₁(F)` then equals
`Unramified.Eigenvalues.eulerPolynomial (Unramified.Eigenvalues.ofTuple z)`.

The proof combines two helper modules. The theorem itself is one line.

- [`OrderedUnramifiedPrincipalSeriesInduction`](OrderedUnramifiedPrincipalSeriesInduction.md)
  (Worker 1789) proves
  `OrderedUnramifiedPrincipalSeries.orderedUnramifiedPrincipalSeriesLPolynomial_of_rankOne`.
  It derives the target from the rank-one proposition
  `OrderedUnramifiedPrincipalSeries.RankOneLPolynomialInput F`, by tail
  divisibility and induction on the tuple length. The induction step uses the
  gamma-factor reflection with rigidity radii `‖z 0‖⁻¹` and `‖z 0‖`.
- [`UnramifiedRankOneLPolynomialProof`](../Representation/RankinSelberg/UnramifiedRankOneLPolynomialProof.md)
  (Worker 1738) proves `RankinSelberg.unramifiedRankOneLPolynomial_eq`. For any
  unitary additive character `ψ`, any additive Haar measure `μ` and any
  `z : ℂˣ`, it identifies every certificate of the rank-one representation
  `characterRepresentation (determinantQuasiCharacter F 1 (Unramified.character F z))`
  against `characterRepresentation (determinantQuasiCharacter F 1 1)` with
  `1 - C z * X`. It computes the scalar Mellin generator and transports the
  pair certificate to it.

The final theorem supplies the rank-one input as
`fun ψ μ z _P hP => RankinSelberg.unramifiedRankOneLPolynomial_eq F ψ μ z hP`.
This typechecks because the two modules write the same two representations,
under the same canonical local instances of `F`.

Provenance: internal composition of the two helper modules. Their own
Markdown files document their routes and the published Library results they
use. No hypothesis is added to the target statement, and no axiom beyond
`propext`, `Classical.choice` and `Quot.sound` is used.
