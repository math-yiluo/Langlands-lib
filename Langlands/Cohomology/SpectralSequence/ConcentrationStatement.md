# Comparison and concentration of cohomological spectral sequences

This pair defines four propositions and their conjunction
`Langlands.Cohomology.SpectralSequenceConcentrationStatements`. The underlying
objects are Mathlib cohomological spectral sequences in an arbitrary abelian
category, with independent object and morphism universes. No theorem is proved
or assumed by these declarations.

The spectral sequence has actual homological complexes for its pages and
isomorphisms from the homology of one page to the next. These are the intrinsic
data of a spectral sequence. They do not include concentration, vanishing
differentials, comparison isomorphisms between arbitrary pages, an abutment,
or an identification with geometric cohomology.

All bidegrees are in \(\mathbb Z^2\). Pages are indexed by integers \(r\geq2\).
The differential has bidegree \((r,1-r)\), so total cohomological degree
increases by one. There is no first-quadrant, boundedness, finite-dimensionality,
coefficient-characteristic, or convergence assumption in these finite-page
statements.

## Declarations

- `SpectralSequenceComparisonStatement`: for an actual morphism of spectral
  sequences, componentwise isomorphisms on page two imply componentwise
  isomorphisms on each subsequent page. The conclusion concerns the same
  morphism, including its commutation with the page-to-homology identifications.
- `SingleColumnDegenerationStatement`: if page two is zero outside a fixed
  column \(p=p_0\), every later page is zero outside that column, all of its
  differentials vanish, and each of its objects is isomorphic to the
  corresponding page-two object.
- `SingleRowDegenerationStatement`: the analogous result for a fixed row
  \(q=q_0\).
- `SinglePositionDegenerationStatement`: if page two is zero outside one
  bidegree, later pages have the same support, zero differentials, and an
  isomorphism at the remaining bidegree.

`IsZero` is the categorical zero-object predicate, not an unspecified
vanishing condition. The later-page isomorphism assertions use `Nonempty`
of the actual category's isomorphism type. They assert existence, without
claiming a chosen natural edge map. No invertibility is assumed to form a page.
The selected conjunction assumes none of its constituent propositions.

## Original sources and derived scope

A. Grothendieck, with J. Dieudonné, *Éléments de géométrie algébrique III,
Première partie*, Chapter 0, Section 11.1, printed pp.23–27 / continuous
pp.367–371:

- Literature ID:
  `provided-bca66cf9ddf1864d04cd9ab13db3799e640164f5476bbe9ed23714ccc825ed03`.
- Registered folder SHA-256:
  `fb65e01feda254662655043bb84b343601696054c02f2c05f42548e66042f1d4`.
- Actual file:
  `literature/EGA III, first part (1961), original containing Chapter 0 §13.2/Grothendieck--Preliminaires (EGA III-1, Chapitre 0, sections 8-13)--1961.pdf`.
- PDF SHA-256:
  `24cb7a75e125f44022411d4b2a86afd2453ab45876945e0ee02b5dd8d5dc5655`.

Section 11.1.1(a)–(c), pp.23–24, supplies the page, differential and homology
data represented by Mathlib's `CohomologicalSpectralSequence C 2`.
Section 11.1.2, p.24, defines the compatible page maps and explicitly explains
propagation of componentwise isomorphisms by induction. This is the first
proposition's source; it asserts nothing about the source's additional abutment
data.

The other propositions are derived fixed-support cases of the elementary
spectral-sequence calculus in Sections 11.1.1 and 11.1.6, p.26. Section 11.1
was read, and p.26 was visually checked in the retained PDF (PDF p.22).
For a fixed column, a differential of bidegree \((r,1-r)\), \(r\geq2\),
cannot have both source and target in the support. For a fixed row the same
holds because \(1-r\ne0\). Hence every differential is zero; passage to its
homology preserves the objects and the support. Induction gives every later
finite page. Single-position concentration is a further specialization.
These fixed-support statements do not use a claim that arbitrary support with
one bidegree on each total-degree diagonal forces all differentials to vanish.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), p.312, equations (5.1)–(5.3) and the paragraph
between (5.1) and (5.2), gives the intended application. Its
Propositions 4.4 and 4.10, pp.309–312, construct the preceding Ext spectral
sequences.

- Literature ID:
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`.
- PDF SHA-256:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- Actual file:
  `literature/Harris (1999), Galois properties of cohomological automorphic forms on GL(n).pdf`.

The entire Harris paper was read during the preceding source audit. For
this application, the first index is Ext degree. Vanishing of higher Ext
and the negative-degree terms would provide a fixed-column hypothesis.
Concentration of the local cohomology would then provide the required
single-position hypothesis. Those geometric and representation-theoretic
vanishing results are separate obligations; they are not hypotheses silently
supplied by this pair.

## Boundaries and dependencies

These statements concern finite pages only. To deduce Harris's cohomology
identification, the actual spectral sequence must still be constructed,
its terms identified, and its convergence and abutment filtration established.
In particular this pair supplies no arbitrary cohomology group, no
postulated comparison isomorphism and no assumed geometric output.
It does not remove the split-place, general-coefficient, unitary/level,
or distinct-prime hypotheses of the eventual Harris application.

The only imported dependency is the pinned Mathlib environment:
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1,
Lean 4.34.0, Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The relevant native implementation is
`Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`.
No unpublished project definition is imported.

These are pending proposition definitions. Compilation, target inspection,
independent semantic acceptance and publication are separate checks; none
constitutes a proof of their truth or of the full Harris theorem.

Authored by Worker 3.
