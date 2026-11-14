# Square-integrability before admissibility (Renard IV.3.2)

This pair defines the square-integrability conditions of Renard IV.3.2 on bundled
smooth complex representations. It uses the existing matrix coefficients,
smooth dual, actual quotient by the group center and descended coefficient norms.
The group universe `uG` and representation-carrier universe `uV` are independent.
The carrier has no topology or finite-dimensionality assumption.

`Langlands.SmoothRep.IsSquareIntegrableModuloCenter π μ` means that there is
a smooth unitary central character acting on every vector of `π`, and that
for every smooth-dual functional `ℓ` and every vector `x`, the descended function
`gZ(G) ↦ ‖ℓ(π(g)x)‖` belongs to `MemLp` with exponent `2` for `μ`.
`MemLp` includes almost-everywhere strong measurability and finite seminorm.
The central character and quotient norm are the actual constructions in
`Langlands.Representation.MatrixCoefficient.ModuloCenter`; no choice of coset
representatives or scalar-action hypothesis is left unverified.

`Langlands.SmoothRep.IsEssentiallySquareIntegrableModuloCenter π μ` means
that some character `ω : G →* ℂˣ` with open kernel has a twist `π ⊗ ω`
satisfying the preceding condition for the same measure. The twist has the same
carrier and action `g ↦ ω(g) π(g)`. Every smooth character is allowed; no selected
positive character or real-exponent restriction is imposed.

Neither predicate includes admissibility or irreducibility. Smoothness is supplied
by the bundled `SmoothRep` argument. This includes reducible smooth representations,
as does the source Definition.

## Original source and the generic construction

- David Renard, *Représentations des groupes réductifs p-adiques*, French version
  dated 9 July 2026, IV.3.1–IV.3.2, printed pages 99–100, PDF pages 105–106.
- Literature ID: `renard-2026-representations-groupes-reductifs-padiques`.
- SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
- Original file:
  `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

IV.3.1 assumes a unimodular t.d. group and fixes a bi-invariant Haar measure on
`G/Z(G)`. IV.3.2 retains these hypotheses. Its Definition requires a unitary scalar
central action and all smooth matrix coefficients in `L²` modulo the center;
essential square-integrability is square-integrability after a character twist.
It does not assume admissibility. The subsequent Proposition proves admissibility
for irreducible essentially square-integrable representations.

The implemented definitions extend the same conditions to any topological group
whose actual central quotient carries the explicitly supplied Borel Haar measure.
They require neither unimodularity nor right invariance to define a predicate.
In particular the measure is required to be Haar, rather than an arbitrary measure.
Applications to the source theorems must retain their t.d.-group and bi-invariance
hypotheses. This generic definitional extension asserts no theorem about such groups.
Using the real norm is necessary: for a nontrivial central character the complex
matrix coefficient itself need not descend to the central quotient.

## Intrinsic comparisons and their proofs

The existing `Langlands.IsSquareIntegrableModCenter` has the additional
admissibility conjunct. `Langlands.SmoothRep.isSquareIntegrableModCenter_iff`
proves by reflexivity that it is exactly
`π.IsAdmissible ∧ π.IsSquareIntegrableModuloCenter μ` on a bundled smooth object.
The old definition and its consumers are unchanged.

`IsSquareIntegrableModuloCenter.isEssentiallySquareIntegrableModuloCenter`
uses the trivial smooth character and the published equality of the trivial
twist with the original action. The theorem
`isEssentiallySquareIntegrableModuloCenter_iff_of_isAdmissible` identifies the
new essential predicate, for an admissible object, with the existence of an
arbitrary smooth twist satisfying the old square-integrability predicate.
Its forward implication uses the published preservation of admissibility by
smooth character twists and adds that conjunct; the reverse implication drops it.
These are intrinsic comparisons of the definitions, not proofs of the source
admissibility or single-coefficient assertions.

The separate `Langlands.IsEssentiallySquareIntegrableModCenter` in
`Langlands.Representation.Classification.Essential` quantifies over real powers
of a specified positive character and uses the admissibility-bearing predicate.
It is a different construction. This pair neither changes it nor asserts that
arbitrary smooth twists reduce to that family.

The all-coefficients premises in the existing
`Langlands.Renard.CompactRepresentation.EssentiallySquareIntegrableAdmissibleStatement`
and IV.3.3 Schur statements already express these source conditions inline.
This pair gives them reusable names without changing their published targets.
The IV.3.2 single-nonzero-coefficient implication remains a separate proof
obligation; no such implication follows merely from these definitions.
