# Compact representations: criterion, admissibility and compact center

Author: Worker 88. The entry theorem `compactRepresentationCriterionStatements`
proves the exact published proposition
`Langlands.Renard.CompactRepresentation.CompactRepresentationCriterionStatements`.
It combines the coefficient-support criterion and finite-type admissibility
proved in the companion modules with the compact-center lemma proved here.

The original is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, IV.1.3 Theorem, Proposition and Lemma,
printed pp.89–90 / PDF pp.95–96, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
All independent group and carrier universes, topological hypotheses, supplied
Haar data in the criterion, and nonzeroness and sigma-compactness in the
center assertion remain exactly as in the published target. No new premise
is introduced.

The coefficient-support theorem is
`compactRepresentationCoefficientCriterion` from
`CompactRepresentationCoefficientCriterionProof`. Its paired Markdown explains
the finite-dimensional projected-orbit span, the finitely many extended smooth
coordinates detecting support, and the inversion homeomorphism matching
`g ↦ π(e_K)π(g⁻¹)x` with the published coefficient convention.
The finite-type proposition is `compactFiniteTypeAdmissible` from
`CompactFiniteTypeAdmissibleProof`. Its paired Markdown explains the finite
sum of projected-orbit spans for group-algebra generators and the resulting
finite-dimensional fixed-vector spaces. These imported proofs establish the
first two exact conjuncts without conditional inputs.

The new theorem `compactRepresentationCompactCenter` proves the Lemma.
Give the group its Borel measurable structure and construct a left Haar
measure internally. The published
`SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial` produces an
actual irreducible smooth subquotient `σ` of the given nonzero smooth
representation `π`, in the same carrier universe. The published
`SmoothRep.hasCompactSmoothDualCoefficients_of_isSubquotient` transfers compact
coefficients to `σ`. Compact-open cofinality supplies its hypotheses and those
of `CompactSplitting.isAdmissible_of_compactCoefficients`, which makes `σ`
admissible. Admissible Schur, in `admissibleSchur_centralCharacter`, supplies
an actual character `χ : Z(G) →* ℂˣ` acting by scalars on `σ`.

Choose a nonzero vector `x` of `σ`. The published smooth-dual separation
theorem applied to the zero subrepresentation supplies a smooth functional
`ℓ` with `ℓ(x) ≠ 0`. For every central element `z`,
`ℓ(σ(z)x) = χ(z) ℓ(x) ≠ 0`, since character values are units. Thus the entire
center lies in the support, hence in the topological support, of this one
smooth coefficient. The coefficient has compact support by compactness of
`σ`. The center is closed: it is the intersection, over `g ∈ G`, of the
closed equalizer sets `{z | gz = zg}`. A closed subset of that compact
topological support is compact, proving the conclusion.

This follows the source's irreducible-subquotient and central-character route,
using a scalar coefficient in place of the vector-valued projected orbit at
the final step. The published admissible Schur theorem suffices; no separate
countable-dimension argument is needed. The target's sigma-compactness
hypothesis is retained. The final entry theorem pairs these three exact
proof terms in the same conjunction order as the Library proposition.
