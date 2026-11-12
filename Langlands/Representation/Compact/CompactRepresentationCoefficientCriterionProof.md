# Compact-support criterion for smooth representations

Author: Worker 88. `compactRepresentationCoefficientCriterion` proves the
exact Library proposition
`Langlands.Renard.CompactRepresentation.CompactRepresentationCoefficientCriterionStatement`.
This is the Theorem component of `CompactRepresentationCriterionStatements`.

The original is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, IV.1.3 Theorem and proof, printed pp.89–90 /
PDF pp.95–96, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The target retains its Hausdorff locally compact totally disconnected
topological group, supplied Borel structure and left Haar measure, and the
independent group and carrier universes. It imposes no irreducibility,
finite generation, admissibility, countability or unimodularity assumption.

Write `P_K` for the published `Hecke.fixedProjection`, the action of the
Haar-normalized subgroup indicator with codomain the fixed-vector space.
The helpers initially use the positive orbit `u(g) = P_K(ρ(g)x)`.

`finiteDimensional_span_projectedOrbit` chooses an independent subset `b` of
the image of `u` spanning the same subspace as that image. Extend `b` to an
algebraic basis `B` of the full fixed-vector space. Its coordinate-sum
functional `B.sumCoords` takes value `1` on each vector of `b`. The published
`CompactCoefficientClass.fixedExtension` extends this functional to a smooth
dual vector `Λ`, and `fixedExtension_apply` identifies its value on a vector
with the original functional applied to `P_K` of that vector. Hence the
smooth coefficient `g ↦ Λ(ρ(g)x)` takes value `1` at every preimage of a
vector in `b`.

This coefficient has compact support by hypothesis. The map `u` is locally
constant, so its image on that compact support is finite: the proof gives
the fixed-vector space the discrete topology locally to apply the compact
image theorem. Every vector of `b` lies in this finite image, so `b` is finite
and its span is finite-dimensional. This generalizes the published
`CompactCoefficientClass.finiteDimensional_fixedVectors` basis argument to
an arbitrary projected orbit. It retains that result and uses its published
smooth-extension construction; no irreducibility step is used here.

`hasCompactSupport_projectedOrbit` now chooses a finite basis of that span
`E`. Extend each coordinate functional from `E` to the full fixed space using
`Subspace.dualLift`, and then extend it smoothly using `fixedExtension`.
The resulting smooth coefficients `C_i` are compactly supported and evaluate
to the coordinates of `u(g)`. If `g` is outside the finite union of their
topological supports, every coordinate of `u(g)` is zero. Thus `u(g) = 0`.
Its support lies in that finite union, which is compact. The compact-support
conclusion follows without a topology on either algebraic representation space.

For the forward implication of the entry theorem, let a smooth functional
`ℓ` be fixed by an open subgroup `L`. Choose a compact open `K ≤ L` by the
published compact-open cofinality theorem. Being fixed under the dual action
means that `ℓ(ρ(k)y) = ℓ(y)` for `k ∈ K`, using the inverse element in that
action. The published `apply_heckeAction_normalizedIndicator` consequently
gives `ℓ(P_K y) = ℓ(y)`. Composing the compactly supported projected orbit
with `ℓ` therefore gives the original coefficient and proves its compact
support.

Inversion of the group is a homeomorphism. Composing by it converts the
positive orbit used by the helpers into the exact target convention
`g ↦ P_K(ρ(g⁻¹)x)`, and converts the assumed inverse orbit into the positive
one when needed. This supplies both directions of the equivalence with the
published `HasCompactSmoothDualCoefficients` predicate and the actual
Haar-normalized fixed projection. It follows Renard's finite-coordinate
support argument with published algebraic smooth-functional extension.
