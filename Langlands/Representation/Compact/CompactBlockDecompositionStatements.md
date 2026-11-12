# Projectivity, injectivity and block decompositions for compact representations: statements

Module `Langlands.Representation.Compact.CompactBlockDecompositionStatements`.
Namespace `Langlands.Renard.CompactRepresentation`.
Entry proposition `CompactBlockDecompositionStatements`.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read IV.1.3–IV.1.7, printed pp.89–96 / PDF pp.95–102. The
assertions stated here are in IV.1.6 (printed p.94 / PDF p.100, proof ending
on printed p.95) and the first part of IV.1.7 (printed p.95 / PDF p.101).

The standing hypotheses are those of IV.1.3–IV.1.4: `G` is a t.d. group,
unimodular and countable at infinity. A representation is *compact* if all its
coefficients have compact support (IV.1.3, Definition and Theorem).

**Notation (IV.1.6).** For an irreducible compact representation `(τ, W)`,
`M(G)_τ` is the full subcategory of `M(G)` of representations that are a direct
sum of irreducible representations equivalent to `(τ, W)`, and `[M(G) \ τ]` is
the full subcategory of representations no irreducible subquotient of which is
isomorphic to `(τ, W)`. For pairwise non-isomorphic irreducible compact
`(τᵢ, Wᵢ)`, `i = 1, …, r`, `[M(G) \ τ₁, …, τᵣ]` is the full subcategory of
representations no irreducible subquotient of which is isomorphic to one of the
`(τᵢ, Wᵢ)`. `M(G)_c` is the full subcategory of representations all of whose
irreducible subquotients are compact, and `Irr(G)_c` is the set of isomorphism
classes of irreducible compact representations.

The four assertions are:

> La catégorie `M(G)_c` est donc semi-simple, et tout module simple y est à la
> fois projectif et injectif.

> **Proposition.** Toute representation compacte irréductible `(τ, W)` de `G`
> est projective et injective dans `M(G)`.

and, in IV.1.7, the three displays `M(G) = M(G)_τ × [M(G) \ τ]`,
`M(G) = ∏ᵢ M(G)_{τᵢ} × [M(G) \ τ₁, …, τᵣ]` and
`M(G)_c = ∏_{τ ∈ Irr(G)_c} M(G)_τ`. Products of categories are in the sense of
A.IX.

## The objects

- Smooth representations are `SmoothRep.{0, u, v} ℂ G`, with group universe
  `u` and carrier universe `v`. Irreducibility is the published
  `SmoothRep.IsIrreducible`. "Compact" is the published
  `HasCompactSmoothDualCoefficients` (every coefficient `g ↦ λ(π(g) v)` with
  `λ` smooth has compact support), Renard's notion by the IV.1.3 Theorem.
- `Irr(G)_c` is the published `CompactCoefficientClass.{u, v} G`, the
  isomorphism classes of objects of `IrreducibleCompactCoefficientRep`
  (irreducible with compact coefficients); `CompactCoefficientClass.ofRep`
  sends such an object to its class.
- Subquotients are the published `SmoothRep.IsSubquotient`, and
  `SmoothRep.subrepresentation V W` is the subrepresentation `W` of `V` as an
  object of `M(G)`.
- `M = ∏ᵢ Mᵢ` is the published `Renard.IsCategoryDecomposition` (A.IX): every
  object is the vertex of a coproduct cofan of objects of the components, and
  every morphism between objects of distinct components is zero.

Three object properties are defined in this file.

- `compactPart G` is `M(G)_c`: `V` such that every irreducible `π` with
  `SmoothRep.IsSubquotient π V` has compact coefficients. It is the same
  predicate as `compactPart` inside the published
  `CompactSplittingCriterionStatement` (IV.1.7, Proposition).
- `isotypicPart G c` is `M(G)_τ` for the class `c` of `τ`: there are a type
  `ι : Type v` and subrepresentations `W : ι → Subrepresentation V.representation`
  with `iSupIndep W` and `iSup W = ⊤` (so `V` is their internal direct sum),
  each `SmoothRep.subrepresentation V (W i)` being irreducible with compact
  coefficients and of class `c`. An index type in `Type v` is enough, since the
  family can be indexed by a set of subrepresentations of `V`. The empty family
  is allowed, so the zero representation lies in every `M(G)_τ`, as for an
  empty direct sum.
- `avoidingPart G S` is `[M(G) \ τ₁, …, τᵣ]` for the set `S` of the classes of
  the `τᵢ`: for every irreducible `π` with compact coefficients that is a
  subquotient of `V`, the class of `π` is not in `S`. An irreducible
  subquotient isomorphic to some `τᵢ` is compact, so this is the same as "no
  irreducible subquotient is isomorphic to one of the `τᵢ`".

## The Lean statements

Every statement quantifies over the same group data as the published IV.1.4
and IV.1.7 statements (`CompactIsotypicComplementStatement`,
`CompactSplittingCriterionStatement`): `G : Type u` a Hausdorff, locally
compact, totally disconnected topological group that is `SigmaCompactSpace`
(countable at infinity), with its Borel structure and a regular Haar measure
`μ` that is also right invariant. The measure only expresses unimodularity and
does not occur in the bodies.

### `CompactProjectiveInjectiveStatement` (IV.1.6, Proposition)

For every irreducible `τ` with compact coefficients, `Projective τ ∧ Injective τ`
in the category `SmoothRep.{0, u, v} ℂ G`. These are Mathlib's categorical
`Projective` and `Injective`.

### `CompactPartSemisimpleStatement` (IV.1.6, sentence before the Proposition)

Two conjuncts:

1. every `V` with `compactPart G V` is a semisimple representation
   (`Representation.IsSemisimpleRepresentation V.representation`, Mathlib's
   notion: every subrepresentation has an invariant complement). This is
   "`M(G)_c` est semi-simple".
2. for every `V` with `hV : compactPart G V` that is irreducible, the object
   `⟨V, hV⟩` of the full subcategory `(compactPart G).FullSubcategory` is
   `Projective` and `Injective` in that full subcategory. The simple objects of
   `M(G)_c` are exactly these `V`, since an irreducible object is a subquotient
   of itself and hence compact. This is "tout module simple y est à la fois
   projectif et injectif".

The source writes "donc" after the Corollary of IV.1.6; the Corollary's
argument applies verbatim to every object of `M(G)_c`.

### `IsotypicSplittingStatement` (IV.1.7, first display)

For every class `c : CompactCoefficientClass G`,
`Renard.IsCategoryDecomposition (fun b : Bool => if b then isotypicPart G c else avoidingPart G {c})`,
that is `M(G) = M(G)_τ × [M(G) \ τ]`.

### `FiniteIsotypicSplittingStatement` (IV.1.7, second display)

For every finite set `S : Finset (CompactCoefficientClass G)`,
`Renard.IsCategoryDecomposition` holds for the family indexed by `Option S`
whose component at `some c` is `isotypicPart G c` and at `none` is
`avoidingPart G S`. That is `M(G) = ∏ᵢ M(G)_{τᵢ} × [M(G) \ τ₁, …, τᵣ]`. A family
of pairwise non-isomorphic irreducible compact `τ₁, …, τᵣ` is the same as the
finite set of their classes. The first display is the case `S = {c}`, with
index `Option {c}` in place of `Bool`; it is stated separately because the
source states it separately.

### `CompactPartDecompositionStatement` (IV.1.7, third display)

In the category `(compactPart G).FullSubcategory`,
`Renard.IsCategoryDecomposition` holds for the family indexed by
`CompactCoefficientClass G` whose component at `c` is the set of objects `X`
with `isotypicPart G c X.obj`. That is `M(G)_c = ∏_{τ ∈ Irr(G)_c} M(G)_τ`.
Coproducts and zero morphisms are those of the full subcategory.

### `CompactBlockDecompositionStatements`

The conjunction of the five statements, at independent universes `u` (group)
and `v` (carriers).

## Formal choices

- Each assertion is posed at a single carrier universe `v`, for all objects and
  for the representatives of the classes, as in the published IV.1.4 and IV.1.7
  statements. The categorical notions (projective, injective, coproduct) are
  those of `SmoothRep.{0, u, v} ℂ G`.
- `M(G)_τ` is indexed by the class of `τ` rather than by `τ`, so that
  `Irr(G)_c` can index the third display; `isotypicPart` uses only membership
  of each summand in the class.
- Renard's hypotheses (unimodular, countable at infinity) are kept as binders,
  although the Proposition does not need them for projectivity: the published
  `Langlands.CompactCoefficient.projective_of_hasCompactSmoothDualCoefficients`
  proves `Projective τ` for every Hausdorff, locally compact, totally
  disconnected `G`.

## Relation to published work

- IV.1.6, Corollary (every compact representation is semisimple) is the
  published `CompactCoefficientSemisimplicityStatement` (Bernstein–Zelevinsky
  2.44(b)), proved by `Langlands.compactCoefficientSemisimplicity`.
- IV.1.7, Proposition (splitting under (KF)) is the published
  `CompactSplittingCriterionStatement`.
- IV.1.4, Theorem and IV.1.5, Proposition (iii) are the published
  `CompactIsotypicComplementStatement`; it is the main input of the first two
  displays of IV.1.7.

## Scope

This file states the assertions and proves none of them. Proofs belong to a
separate `lean.proof@1` task targeting `CompactBlockDecompositionStatements`. The source's proofs use the
projectors `π(e_τ)` of IV.1.5, Lemma A.VII and the IV.1.4 Theorem.

The file imports `Langlands.Representation.CompactCoefficient.Classes`,
`Langlands.Representation.Category.Subquotients`,
`Langlands.Representation.SubrepresentationLattice`,
`Langlands.CategoryTheory.RenardCategoryDecomposition`, and pinned Mathlib
`Mathlib.CategoryTheory.Preadditive.Projective.Basic`,
`Mathlib.CategoryTheory.Preadditive.Injective.Basic`,
`Mathlib.RepresentationTheory.Semisimple` and
`Mathlib.MeasureTheory.Measure.Haar.Basic` (environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).
