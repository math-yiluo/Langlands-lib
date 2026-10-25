# Finite-length head multiplicity and intertwiner dimension

This file states an internal algebraic interface for converting dimensions of
intertwiner spaces into Jordan–Hölder multiplicities. It contains proposition
definitions, not proofs.

`Langlands.Classification.FiniteLengthHeadHomMultiplicityStatement` is the
conjunction of the following two closed propositions. In both, the group universe
`uG`, the source-carrier universe `uV`, and the target-carrier universe `uW` are
independent. The group `G` has an arbitrary topology.

- `HeadHomMultiplicityStatement` quantifies complex representations `A` and `τ`
  of `G`. If the group-algebra module `A.ρ.asModule` has finite length, and `τ`
  is admissible and irreducible, then the complex space
  `A.ρ.IntertwiningMap τ.ρ` is finite-dimensional. It also asserts
  `HasJordanHolderMultiplicity (Rep.of (head A.ρ)) τ
  (Module.finrank ℂ (A.ρ.IntertwiningMap τ.ρ))`.
- `SemisimpleHomMultiplicityStatement` makes the same assertion about the
  intertwiner space when `A` has finite length and is semisimple, and asserts the
  displayed multiplicity for `A` itself.

Here `HasJordanHolderMultiplicity` means that an actual finite composition
filtration exists, all its graded factors are simple, and exactly the stated
number of those factors are equivalent to `τ`. Thus each conclusion includes
composition-series existence, including when the dimension and multiplicity
are zero. The statements assert finite-dimensionality separately, so the
`finrank` is the dimension of a finite-dimensional space.

The source is not required to be smooth or admissible, or to have a
finite-dimensional complex carrier. There is no topological-group assumption.
The hypotheses prescribe neither a composition series nor a decomposition.
Only the semisimple-source clause assumes source semisimplicity; the head clause
uses the existing actual quotient `Classification.head`.

The imported `Classification.Cosocle` identifies that quotient as the finite-length
cosocle and supplies its universal property, including for targets in independent
carrier universes. The imported `Smooth.Schur.Proof` supplies
`Langlands.admissibleSchur_scalarEndomorphism` and
`Langlands.admissibleSchur_homEquiv`. Admissibility of the target contains the
smoothness used by those Schur results. The present file defines no replacement
cosocle and proves no new cosocle or Schur laws. It reuses the multiplicity
predicate from `Filtration.MultiplicityStatement`.

The provenance is an internal derived algebraic interface. Silberger's use of
Frobenius reciprocity and quotient multiplicities in Proposition 5.9, p. 102 of
*The Langlands quotient theorem for p-adic groups* (1978), motivates this bridge
for the relative cosocle comparison. The present arbitrary-group and
independent-carrier quantifiers are not attributed to that proposition. A
separate proof must establish both clauses, using semisimple algebra and Schur's
lemma, and transport the head clause through the published head universal
property.
