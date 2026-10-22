# Actual Jordan–Hölder factor matching from matching graded pieces

Author: Worker 250. Coauthors: Worker 242, who proposed this mathematical
interface, and Worker 34, who prepared the focused statement contract.
Provenance: internal derived module-theoretic content (see below).

The proposition definition `Langlands.GradedJordanHolderRefinementStatement`
in `Langlands.Representation.Filtration.GradedRefinementStatement` states one
existence claim about the Library's actual representation filtrations. It
does not prove that claim.

## Statement

The proposition quantifies over the following data:

- a coefficient field `k : Type uK`;
- a monoid `G : Type uG`;
- representations `A : Rep.{uA} k G` and `B : Rep.{uB} k G`;
- a natural number `n`;
- actual finite filtrations `f : ObjectRepFiltration A n` and
  `g : ObjectRepFiltration B n` of the same length;
- a permutation `e : Equiv.Perm (Fin n)`.

The only hypothesis is

```lean
∀ i : Fin n,
  HaveSameJordanHolderFactors (f.gradedRepresentation i)
    (g.gradedRepresentation (e i))
```

The conclusion is `HaveSameJordanHolderFactors A B`.

The graded pieces `f.gradedRepresentation i` and `g.gradedRepresentation j`
are the actual successive quotient representations of the two filtrations.
`HaveSameJordanHolderFactors` is used unchanged from
`Langlands.Representation.Filtration.ObjectDefinitions`. It asserts that
there are actual composition series of the two representations with the same
finite number of factors and a permutation of indices that matches every
factor occurrence through a `Representation.Equiv`. The hypothesis and the
conclusion therefore both keep multiplicities. Neither is replaced by equality
of sets of constituents, by equality of classes in an abstract Grothendieck
group, or by a permutation that ignores multiplicities. The permutation `e`
pairs every graded piece of `f` with exactly one graded piece of `g`.

Only the sole import, `Langlands.Representation.Filtration.ObjectDefinitions`,
is used. `ObjectRepFiltration`, `gradedRepresentation` and
`HaveSameJordanHolderFactors` are used unchanged, and no existing pair is
modified.

## Scope of the quantifiers

- The filtrations `f` and `g` are not required to have simple factors. Their
  graded pieces may be reducible or zero.
- The quantifiers include `n = 0`. A length-zero filtration has equal
  endpoints `⊥` and `⊤`, so then `A` and `B` are zero and the hypothesis is
  vacuous.
- An index whose two matched graded pieces are both zero satisfies the
  hypothesis through two length-zero composition series. Such zero pieces are
  allowed anywhere in either filtration.
- The statement does not assume any of the following: finite dimensionality,
  finite length or an Artinian or Noetherian condition on `A` or `B`,
  smoothness, admissibility, that `G` is a group rather than a monoid,
  nontriviality of the representations, or supplied refinements or
  composition series of `A` or `B`.
- The universes `uK`, `uG`, `uA` and `uB` are independent. Lean inspection
  of the unapplied proposition reports exactly these four level parameters.

## Where the finiteness comes from

No separate finite-length hypothesis is needed, because the matching
hypothesis is itself existential. At each index `i` it supplies an actual
composition series of `f.gradedRepresentation i` and one of
`g.gradedRepresentation (e i)`, both of the same finite length, together with
their factor matching. Since `e` is a bijection, every graded piece of `g`
occurs as `g.gradedRepresentation (e i)` for exactly one `i`. So the
hypothesis supplies a finite composition series for every graded piece of
both filtrations. This is exactly the finiteness that a refinement of `f` and
`g` to composition series of `A` and `B` requires. A blanket finite-length
assumption would add nothing to it. Without the matching hypothesis there
would be no finiteness at all.

## Intended later proof, not proved here

The following plan is recorded for the separate proof task. It is not
evidence for the statement.

For each `i`, take the two series supplied by the hypothesis. Lift the series
of `f.gradedRepresentation i` through the subobject correspondence for the
quotient `f.gradedProjection i`. The result is a chain of invariant subspaces
from `f.subrepresentation i.castSucc` to `f.subrepresentation i.succ`, and
its successive quotients are equivalent to the factors of that series.
Concatenate these chains over `i` to get an actual composition series of `A`.
Its length is the sum of the per-piece lengths. Do the same for `B`, using
for its graded piece `j` the series supplied at index `e⁻¹ j`. A matching of
the concatenated factors comes from two ingredients: `e` permutes the blocks,
and the per-index permutations given by the hypothesis permute the factors
within each block.

This construction differs from supplied-series comparison, the
Jordan–Hölder uniqueness clause of the separate task
`f20dd2de-7590-499c-9d43-feadea1982fb`. That clause compares two arbitrary
composition series of one representation, which needs the Schreier or
Jordan–Hölder argument. Here each graded piece is refined using a series
supplied by the hypothesis, and the matching of each pair is already given.
So the reconstruction only lifts and concatenates; it never compares two
different series of one representation. A later proof may still import
verified helpers from that task, such as transport of a series along an
equivalence. This statement does not depend on them.

## Why the filtrations are not assumed simple

The intended consumer is the adjacent-swap step in task
`0ae6352d-841c-4f54-a8e2-875be492061b`. There, exactness of induction turns a
composition series of a two-block induced representation into a filtration
of a larger induced representation, and that filtration's graded pieces are
inductions of irreducible representations, which need not be irreducible.
If the statement assumed that `f` and `g` have simple factors, then `f` and
`g` would already be composition series. The statement would then only
repackage the definition of `HaveSameJordanHolderFactors` and could not be
applied to those filtrations. Supplying actual composition series of the
matched graded pieces is the consumer's obligation, not part of this
statement.

## Source and motivation

Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups
I*, Ann. Sci. ENS (4) 10 (1977), §§2.16(2)–2.17, printed page 450 / PDF
page 11. Source ID: `bernstein-zelevinsky-1977-induced-i`; original PDF
SHA-256: `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Worker 250 read PDF pages 4 and 7–11 of the registered original on
2026-10-22. Those pages contain §1.2 (JH and JH°), Proposition 2.3, the
statements of Theorems 2.8–2.9 and §§2.14–2.17.

In §2.16, BZ77 proves the implication (i) ⇒ (iii) of Theorem 2.9, that
JH°(π) = JH°(π′), in two steps. Step (1) handles `l(M) = 2`. In step (2)
they call `w : M → N` elementary if `M, N < L`, `w ∈ W_L` and `l(M) = 2`
inside `L`. They say that condition (iii) for `ρ′ = w(ρ)` then "follows from
the preceding step and 2.3 (c), (a)", that is, from induction in stages and
exactness of induction. Lemma 2.17 writes every `w` as a composition of
elementary maps.

The present statement isolates one algebraic principle that this one-sentence
reduction leaves implicit. Exactness carries a composition series of a
representation of `L` to a filtration of the induced representation of `G`
whose graded pieces need not be simple. Equality of JH° for the two
representations of `G` then follows from JH°-matching of the graded pieces.
The chaining along Lemma 2.17 uses transitivity of factor matching. That is a
different clause, owned by the separate task above, and is not part of this
statement.

BZ77 does not state this principle separately, and the proposition is not a
verbatim statement from the source. BZ77 works with smooth (algebraic) complex
representations of l-groups and JH° of finite-length representations. The
field-and-monoid formulation with actual filtrations and multiplicity-sensitive
matching is derived module-theoretic content. It is broader in its algebraic
generality and makes no claim about smooth or admissible representation
theory beyond what it literally states.
