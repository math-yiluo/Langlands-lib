# Renard A.II.2: proof of the fixed-dimension vector-space equivalence

`Langlands.Renard.fixedDimensionVectorSpaceEquivalence` proves exactly
`Langlands.Renard.FixedDimensionVectorSpaceEquivalenceStatement k n`.
The implementation is by Worker 1158 following the proof route supplied
by Worker 709, who authored the published construction and statement.
The proof imports those pairs and the general equivalence criterion by
Lean name, without changing them.

## Source and exact target

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, A.II.2, printed p.251 / PDF257.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original page was read and visually inspected. Its example asserts
that the inclusion of the one-object category on `kⁿ`, with every linear
endomorphism, into the category of dimension-`n` vector spaces, with every
linear map, is an equivalence. The following paragraph explains the
choice of coordinate identifications for all objects.

The imported [statement](FixedDimensionVectorSpacesStatements.md) uses
the correctly typed identity categories: for an inclusion `F : C ⥤ D`
and reverse functor `G : D ⥤ C`, Lean's application-order composition
gives `F ⋙ G ≅ 𝟭 C` and `G ⋙ F ≅ 𝟭 D`. This retains the correction of
the exchanged identity-category subscripts in the source's boxed
quasi-inverse definition, documented in the
[criterion statement](EquivalenceCriterionStatements.md).

The actual [construction](FixedDimensionVectorSpaces.md) defines
`FixedDimensionVectorSpaces k n` as the full subcategory of `ModuleCat k`
on objects satisfying both `FiniteDimensional k X` and
`Module.finrank k X = n`. The explicit finite-dimensionality condition
also handles `n = 0`, since finrank alone can vanish for an
infinite-dimensional space. The coordinate object is
`ULift.{v} (Fin n → k)`, and `OneObjectVectorSpaceCategory k n` is its
actual full singleton subcategory. The functor in this proof is precisely
`fixedDimensionVectorSpaceInclusion k n`.

## Implemented proof

The proof applies the published
[`equivalenceCriterion`](EquivalenceCriterion.md) to that inclusion.
It discharges the criterion's three hypotheses as follows:

1. For every pair of source objects, `map_surjective` supplies surjectivity
   of the actual Hom map. All ambient linear maps between the selected
   objects are retained by the full-subcategory inclusion.
2. For the same objects, `map_injective` supplies injectivity of that Hom
   map, using the inclusion's faithful instance.
3. For each ambient object `X`, the source witness is
   `oneObjectVectorSpace k n`. Its image is definitionally the coordinate
   object, so `coordinateVectorSpaceIso k n X` gives the required actual
   isomorphism from that image to `X`.

The coordinate isomorphism is already constructed using
`LinearEquiv.ofFinrankEq`, the defining dimension equalities, and the
finite-dimensionality instances. Its classical choice of bases is
inherited unchanged. No choice of bases is taken as an added premise.

The criterion produces one actual reverse functor and both natural
isomorphisms for that same functor. Its implementation uses
`Functor.asEquivalence.inverse`, `unitIso.symm` and `counitIso`.
Consequently the conclusion contains actual isomorphisms in the functor
categories, including naturality and inverse laws; the objectwise
coordinate isomorphisms serve as input to that categorical construction.
This reuses the published criterion and pinned Mathlib machinery rather
than transcribing a proof from Renard's cited references.

The theorem retains independent universe parameters `u` and `v`: the
field is `k : Type u`, and vector-space carriers lie in
`Type (max u v)`. Its only assumptions are `[Field k]` and the natural
parameter `n`; every natural dimension, including zero, is covered.
The result proves the stated equivalence for the prescribed inclusion.
It adds no uniqueness, strict-inverse or triangle-identity requirement,
and makes no completion claim about the other A.I–A.II assertions.
