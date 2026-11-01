# Renard II.1.1: locally profinite space and group statements

This statement-only unit records the four results following Renard's definition
of a t.d. space. Every target is a transparent `Prop`-valued `def` in
`Langlands.Topology.LocallyProfiniteStatements`. No proof of a target is supplied.
The imported, published `Langlands.Topology.IsLocallyProfinite` means exactly a
Hausdorff space with a compact-open neighborhood basis.

## Original source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**, II.1.1, printed page 30 / PDF page 36:

- The paragraph after the space definition gives the compact-open subgroup
  characterization and names Van Dantzig's theorem for necessity.
- Lemma (i) concerns locally closed subspaces.
- Lemma (ii) concerns finite subordinate covers by disjoint compact opens.
- The following unnumbered proposition states the Baire property as density
  of a countable intersection of dense opens.

The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 6 read the entire governing page and its proof paragraphs.

The supplementary registered source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
Its PDF page 2 corrects the older edition's Baire wording. The governing 2026
page already has the corrected density assertion. This supplementary check
does not replace the 2026 statement.

The four statements translate these source assertions. The finite indexing
by `Fin n`, arbitrary countable index type, and conjunction are formal packaging.
The explicit Hausdorff conjunct in the group characterization retains the
source's separation convention.

## Exact targets

`VanDantzig` universally quantifies an actual group `G`, its supplied topology,
and `IsTopologicalGroup G`. It asserts that `IsLocallyProfinite G` is equivalent
to the conjunction of `T2Space G` and the following condition: for every
neighborhood `U` of `1`, there is an actual `OpenSubgroup G` whose underlying
set is compact and lies in `U`. An open subgroup contains `1`, so this is
precisely a compact-open subgroup neighborhood basis at the identity.
There is no `NonarchimedeanGroup`, global compactness, countability or
local-profinite hypothesis on the right beyond the displayed conditions.

The source introduces t.d. spaces as Hausdorff. Compact-open subgroup bases
alone do not imply Hausdorffness: the indiscrete topology on a nontrivial finite
group has such a basis. The explicit `T2Space G` conjunct therefore records
the source's intended separated-group context and makes both directions
precise.

`LocallyClosedSubspaces` quantifies every locally profinite `X` and every
`Y : Set X` satisfying Mathlib's `IsLocallyClosed Y`. Its conclusion is
`IsLocallyProfinite Y` for the actual subtype topology. The source recalls
the equivalent local definition: each point of `Y` has an ambient neighborhood
in which `Y` is closed. Mathlib's
`isLocallyClosed_iff_isLocallyClosedAt` provides that correspondence.
The statement permits empty subspaces and imposes no global closedness.

`FiniteDisjointRefinement` quantifies every compact `K : Set X` in a locally
profinite space and every open cover `U : I → Set X` of `K`. It returns a
natural number `n` and sets `V : Fin n → Set X` such that:

1. Every `V j` is open and compact in the ambient topology.
2. Distinct indices have disjoint sets.
3. Their union contains `K`.
4. Each `V j` is contained in some member of the original cover.

The refining sets need not be contained in `K`, and their union need not equal
`K`. No global compactness of `X` or finiteness of the original cover is
assumed. The case `K = ∅`, including an empty original cover, is permitted
and can be witnessed by `n = 0`. Empty refining members are allowed.
Each subordinating index exists separately; no coverage of all the original
open sets is claimed.

`DenseOpenIntersections` quantifies every locally profinite `X`, every
countable index type `I`, and every family of open dense subsets of `X`.
It asserts that their intersection is dense. Countability applies only to
the family, with no second countability, sigma compactness or cardinality
restriction on `X`. Empty families and empty spaces are included.

`LocallyProfiniteAssertions` is exactly the conjunction of these four closed
targets in that order. The space/group universe `uX` and family universe `uI`
are independent; the locally closed subtype and the finite refinement live
in the original space universe. The group and topology instances are those
universally quantified in each target.

## Proof obligations and dependency boundary

The public project import is `Langlands.Topology.LocallyProfinite`; the
additional Mathlib import is `Mathlib.Topology.LocallyClosed`. This pair
introduces no new objects, replacement topology or axioms. The approved
environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

The source proves the subspace and refinement lemmas directly, cites Van
Dantzig for the subgroup necessity, and cites [26], Theorem XI.10.1, for Baire.
A proof successor must prove the unchanged published targets. The existing
definition module's subgroup-basis lemma retains a `NonarchimedeanGroup`
assumption, so it does not discharge the forward Van Dantzig target here.
No Chapter II completion, function/distribution construction or theorem proof
is claimed by this statement unit.
