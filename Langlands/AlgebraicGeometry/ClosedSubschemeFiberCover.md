# Finite closed covers of actual fibres

This derived construction isolates the finite closed-cover step in Stacks Project
Lemma 37.28.4 (055G), as a prerequisite for the geometric-connectedness input to
Conrad's Theorem 3.4(2). The registered source is
`stacks-fibre-constructibility-local-dimension-2026-11-04`, retained `055C.html`,
Lemma 37.28.4, the paragraph beginning with the decomposition of the generic
fibre and the shrinking that makes the closures cover the source. The source
invokes Lemma 37.24.5 for that step. Here the explicitly retained Noetherian
hypothesis permits a direct proof using Mathlib's Chevalley theorem.

All schemes have arbitrary common universe `u`; the index type has independent
universe `v`. The construction and its range comparisons allow arbitrary index
families and arbitrary morphisms into the source. The shrinking theorems require
a finite family of closed immersions, a locally finite-type quasi-compact
morphism `f : X ⟶ Y`, a Noetherian scheme `Y`, and a point generic for the whole
base. There is no affine, flat, proper, smooth or separation hypothesis. The
empty indexing family is allowed and tests emptiness of the actual fibre.

## Actual cover and comparisons

`closedSubschemeFiberCover f g y` says the union of
`fiberSubschemeSets f g y i` is the whole scheme-theoretic fibre `f.fiber y`.
The imported construction takes inverse images of the actual ranges of `g i`
under the actual fibre projection. `closedSubschemeFiberCover_iff_baseChangeRanges`
identifies coverage with coverage by the ranges of the actual projections from
`pullback (g i) (f.fiberι y)` to `f.fiber y`.

`closedSubschemeFiberCover_iff` proves that coverage is equivalent to `y` not
belonging to the image under `f` of the complement of the union of those ranges
in `X`. The proof uses the exact actual-fibre nonemptiness/image comparison and
the fact that inverse images commute with unions and complements. These
comparisons impose no finiteness or closedness assumption.

## Generic shrinking

`exists_open_closedSubschemeFiberCover` proves constancy of the truth value of
coverage on an open neighbourhood of the supplied generic point. Finite type
over the Noetherian base makes `X` Noetherian. The union of the finitely many
closed ranges is closed, so its complement is a compact open, hence
constructible. Chevalley makes its image constructible. The imported generic
constructible-membership theorem gives a neighbourhood where membership in
this uncovered image is constant; the actual cover comparison negates that
membership equivalence.

`exists_open_closedSubschemeFiberCover_of_generic` applies this to a cover of
the generic fibre, obtaining coverage of every fibre over that neighbourhood.
Since the open set contains the generic point, it is nonempty.
`exists_open_closedSubschemeFiberCover_and_incidence` intersects that
neighbourhood with the one supplied by the previously constructed incidence
theorem. It preserves both the coverage predicate and every pairwise incidence
predicate throughout one open set.

These are proved intrinsic construction and comparison lemmas. They do not
construct closures of generic irreducible components, prove geometric
irreducibility of their nearby fibres, compare field extensions, or prove the
full geometric-connectedness or filtered-descent assertions. The source's
non-Noetherian generality remains a separate obligation.
