# Langlands heads in reversed standard modules

Module `Langlands.Representation.Classification.LanglandsSubrepresentationStatement`,
namespace `Langlands.Classification`. Worker 353 prepared this statement from Worker 5735's
Task 5735 revision-4 draft; the proposition is unchanged. This module contains a
Prop-valued definition, `LanglandsSubrepresentationRealization`, and no proof of it.

## Exact statement and conventions

The target quantifies over every prime `p`, every actual `F : PadicField.{uF} p`, every
`T : F.TopologicalData`, every rank `n : ℕ` and every
`d : T.SegmentProductDatum.{max uF uV, uF} n`. The field universe `uF` and the carrier
parameter `uV` are independent; the blocks and output representations have carriers in
`Type (max uF uV)`. No finite-dimensionality restriction is imposed.

The two hypotheses on `d` are:

- `d.HasSegmentHeads`: each actual block is the strong irreducible head of the increasing
  induction of its segment, `ρ × νρ × ⋯ × ν^(m-1)ρ`, where `ν = |det|_F`.
- `∀ i j, i < j → ¬ (d.segments j).Precedes (d.segments i)`: no later segment precedes
  an earlier one.

Here the products are actual normalized inductions from standard upper block parabolics,
with right translation and covariance `f(pg) = δ_P(p)^(1/2) σ(p) f(g)`.
The absolute value is normalized by `|ϖ|_F = q^(-1)`. The special head is the essentially
square-integrable constituent, denoted `δ(Δ)` by Jantzen; it is distinct from the segment
socle of the increasing induction. `Precedes` means that the segments are linked and that
the second beginning is a strictly positive integral norm twist of the first beginning.
The displayed order reverses the condition in `SegmentProductDatum.IsPrecedenceOrdered`,
which forbids an earlier segment from preceding a later one. It imposes no order on
unlinked pairs.

For every such datum the target asserts both:

1. Every `π` satisfying `d.multisegment.IsLanglandsHead π` embeds into `d.induced`.
2. Every irreducible `π` that embeds into `d.induced` satisfies
   `d.multisegment.IsLanglandsHead π`.

`d.multisegment` retains all segment multiplicities. Its `IsLanglandsHead` relation is
the existing existential relation from `LanglandsData`: for some ordering forbidding
earlier-before-later precedence and some actual segment heads, `π` is the strong
irreducible head of the resulting product. `SmoothRep.IsSubrepresentation π d.induced`
means that there exists an actual injective intertwiner from `π` to `d.induced`.
The first clause therefore needs no additional irreducibility premise on `π`; the head
relation already supplies it.

The target itself states two implications. Together with the separate head-existence and
head-classification results, they give existence and uniqueness up to isomorphism of an
irreducible subrepresentation of the reversed product. This statement does not assert
that all irreducible embeddings have the same image or assert multiplicity one.

Rank zero and the empty datum are included. Since every segment has positive degree,
total degree zero forces an empty family. Its normalized product is the empty tensor
product, the one-dimensional trivial representation of `GL_0(F)`. This boundary case is
a derived extension of the positive-rank classification, not an added hypothesis.

## Source correspondence and derived formulation

Jantzen 2007, §1.2, pp.47–48 fixes the normalized product and the increasing-segment
quotient `δ(Δ)`. On p.49 he recalls that a product of essentially square-integrable
blocks with weakly increasing unitary exponents has a unique irreducible subrepresentation.
Page 50 also permits data whose induced products are isomorphic to the Langlands standard
product. Zelevinsky 1980, §9.1, p.197 identifies the same special representation as the
quotient of the increasing segment induction and as the submodule of the decreasing
segment induction. Sections 3.3 and 9.4 describe endpoint-reversed segment duality.

The target is the derived reversed-precedence formulation using the Library's existing
head relation. To explain its ordering, dualize every segment `[ρ, ρ']` to
`[ρ'ᵛ, ρᵛ]`. The Library's `Segment.precedes_dual_iff` reverses precedence, so keeping
the index order converts the target's reversed condition into `IsPrecedenceOrdered` for
the dual segments. The smooth dual of the normalized product is the normalized product
of the smooth dual blocks in that same order; the blocks remain special heads.
Duality identifies Langlands heads for a multisegment with those for its dual multisegment.
A quotient of the dual product then dualizes to an embedding into the original product;
an irreducible embedding conversely dualizes to an irreducible quotient. Admissible
biduality supplies the identifications. This explains both clauses without putting any
duality or classification assertion among the target's hypotheses.

Published interfaces relevant to that later proof are
`Parabolic.NaturalNormalizedInductionDualityStatement`,
`PadicField.TopologicalData.IsSegmentHead.contragredient`,
`PadicField.TopologicalData.Segment.precedes_dual_iff`, and
`Classification.MultisegmentConstituentContragredientCompatibility`.
The latter's published target is restricted to positive output rank; the empty case
described above remains a separate boundary case. This paragraph records a proof route,
not a proof implemented in this module. Zelevinsky §9.17 is a duality conjecture in the
printed article and is not used here as a proof of this statement.

The actual-data relations, arbitrary carrier universes, two-implication packaging and
empty-rank extension are formalization choices derived from this source correspondence.
They are not claimed to be literal formulations in the original papers.

## Registered originals and reading extent

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II. On irreducible
  representations of GL(n)*, Ann. Sci. ÉNS (4) 13 (1980), 165–210.
  Literature ID `zelevinsky-1980-induced-ii`;
  SHA-256 `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  Relevant locators: §§3.1–3.3, pp.180–181, and §§9.1, 9.4, pp.197–198.
  Retained file:
  `/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.
  Read PDF pp.17–18 and 34–36, and checked the §9.17 boundary on PDF pp.40–41.
- Chris Jantzen, *Jacquet modules of p-adic general linear groups*, Representation Theory
  11 (2007), 45–83, DOI 10.1090/S1088-4165-07-00316-0.
  Literature ID `jantzen-2007-jacquet-gln`;
  SHA-256 `ac28095d67e62467cca48ca34e268774fdaeac9fb6adb5231750d4eb98d22530`.
  Locator: §1.2, pp.47–50 (PDF pp.3–6), especially the classification paragraph on p.49
  and the induced-product equivalence convention on p.50.
  Retained file:
  `/home/taskhub/central-library/Jantzen--Jacquet modules of p-adic general linear groups--2007.pdf`.
  Read those four PDF pages.

No complete-paper reading is claimed. No source-specific errata note for either work
was found in the current Library's `notes/errata` directory.
