# Admissibility of irreducible representations with compact coefficients

Worker 340, using the statement draft by Worker 307. This module defines a
proposition; it supplies no proof of that proposition.

## Statement and interfaces

`Langlands.CompactCoefficientIrreducibleAdmissibilityStatement.{uG,uV}`
asserts that every irreducible smooth complex representation of a Hausdorff,
locally compact, totally disconnected topological group is admissible if
all its smooth-dual coefficients have compact support.

The group is `G : Type uG` with `Group`, `TopologicalSpace`,
`IsTopologicalGroup`, `T2Space`, `LocallyCompactSpace`, and
`TotallyDisconnectedSpace` instances. The actual representation is
`A : SmoothRep.{0, uG, uV} ℂ G`; its carrier universe `uV` is independent
of `uG`. Smoothness is part of this bundled object. Its carrier has no topology.

The hypotheses use the published predicates:

- `A.IsIrreducible` is simplicity of the lattice of invariant submodules,
  including nonzeroness.
- `HasCompactSmoothDualCoefficients A.representation` means that for every
  vector `v` and every algebraic linear functional `ℓ` smooth under the dual
  action, the function `g ↦ ℓ (A.representation g v)` has compact support.

The conclusion `A.IsAdmissible` is the existing all-open-subgroups predicate:
smoothness and `Module.Finite ℂ (fixedVectors A.representation K.toSubgroup)`
for every `K : OpenSubgroup G`. Over the complex field this is
finite-dimensionality of each actual fixed subspace. The representation
itself need not be finite-dimensional. No finite dimension, finite length,
admissibility, central character, dimension bound, sigma-compactness,
unimodularity, or choice of Haar measure is assumed.

The sole import is `Langlands.Representation.CompactCoefficient.Classes`,
which supplies the coefficient predicate and imports the existing smooth
representation interfaces. Existing Library modules are unchanged.

## Original source and derived provenance

The provenance is `derived`: this is the irreducible specialization of the
stronger finitely generated statement in Bernstein–Zelevinsky (1976),
Corollary 2.41, with the source conventions expressed through the published
Library predicates. A nonzero vector generates an irreducible representation
as a group representation, so this specialization adds no finite-generation
hypothesis. The source also explicitly singles out irreducibles.

The registered original is I. N. Bernshtein and A. V. Zelevinskii,
*Representations of the group GL(n,F) where F is a non-Archimedean local field*,
Russian Mathematical Surveys **31**:3 (1976), 1–68, English translation.

- Literature ID: `bernstein-zelevinsky-1976-representations-gln`.
- SHA256: `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- Retained PDF: `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
- Locators: §1.1, p.6 (locally profinite groups); §2 introduction and
  §§2.1–2.4, pp.14–16 (complex representations without a carrier topology,
  irreducibility, smoothness, admissibility, and compact-subgroup projection);
  §§2.13–2.14, p.19 (smooth contragredient and fixed duals);
  §§2.39–2.41, p.26 (coefficients, finite representations, and admissibility).
  PDF page indices equal these printed page numbers.

The source's “algebraic” representation means smooth in the present sense.
Its contragredient is the smooth part of the full algebraic dual under the
inverse action, exactly the functionals quantified by
`HasCompactSmoothDualCoefficients`. Its “finite” representation means that
all these coefficient functions have compact support; it does not mean
finite dimension. Section 2.39 writes the coefficient with `g⁻¹`, whereas
the Library writes it with `g`. Inversion is a homeomorphism of a
topological group and preserves compact support. These coefficients are
locally constant, so their nonzero loci are closed and the support
convention agrees with Mathlib's compactness of the closure of the nonzero
locus.

The source works with locally profinite groups (§1.1). For a Hausdorff,
locally compact, totally disconnected topological group, compact open
subgroups form a neighborhood basis of the identity. This identifies
the Lean hypotheses with that setting, without a countability hypothesis.

Definition 2.1(b) already states admissibility for all open subgroups.
The proof of 2.40 establishes the relevant finite-dimensionality using
compact open subgroups. To pass from that compact-open criterion to the
Library's all-open-subgroup convention, take any open subgroup `K` and
choose a compact open subgroup `N` contained in `K`. Then
`V^K ⊆ V^N`; a subspace of a finite-dimensional complex vector space is
finite-dimensional. This explains the convention comparison without
adding a cofinality or admissibility hypothesis.

## Proof boundary

The proof of 2.40 shows that, for each vector and compact open subgroup,
the span of the compact-open averages of its orbit is finite-dimensional.
For an irreducible representation a nonzero vector generates the whole
representation; its averaged orbit therefore spans that subgroup's fixed
space. These observations explain the source's corollary and the
specialization. They are mathematical explanations, not additional Lean
claims or a formal proof supplied by this module. In particular, this
statement does not assert a uniform dimension bound or fixed-level
finiteness of isomorphism classes.
