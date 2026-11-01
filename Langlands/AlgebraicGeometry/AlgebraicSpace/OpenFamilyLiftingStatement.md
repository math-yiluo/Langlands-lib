# Lifting a covering family of open scheme charts across a thickening

Author: Worker 148. The interface design is due to Workers 336 and 133.

The module defines
`Langlands.AlgebraicGeometry.AlgebraicSpace.OpenFamilyLiftingStatement`,
a proposition at arbitrary universe `u`. It states the lifting of an indexed
covering family of open scheme charts across an unrestricted thickening of
actual algebraic spaces over any base scheme. It supplies no proof of that
proposition.

## Original source and derived formulation

The registered original is
`stacks-algebraic-space-thickenings-2026-11-01`, directory SHA-256
`ccb6ba86c00dce19994e249af819e4ed6aa7958b0fff47061565d127630d29da`,
retained at
`/home/taskhub/pilot/literature/Stacks Project - Closed immersions and thickenings of schemes and algebraic spaces (HTML snapshot 2026-11-01)`.
The relevant original passages in `05ZJ.html`, also read in its full text aid
`05ZJ.txt`, are:

- [Definition 76.9.1, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK):
  a thickening is a closed subspace with unchanged underlying topological space.
- [Lemma 76.9.3, Tag 05ZP](https://stacks.math.columbia.edu/tag/05ZP):
  each open subspace of the smaller space has a unique open lift whose
  pullback is that subspace.
- [Lemma 76.9.8, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX):
  arbitrary base change of a thickening is a thickening.

The retained section has no comments. No source-specific errata file was found
in the checked project, Library or workspace `notes/errata/` locations.
The live Tag 05ZP statement and proof agree with the retained original.

The Lean proposition is an internal family formulation derived from these
passages, rather than a verbatim statement of Tag 05ZP. Each open immersion
from a represented scheme identifies an open subspace of `X`; applying the
single-open lifting separately and choosing the lifts gives the family `V`
with the original indices. Tag 05ZP also gives uniqueness, which this
existence-only interface does not request. In each pullback square, `c k`
is the base change of `i`, so its thickening property is a separate
base-change consequence, as in Tag 09ZX.

The additional covering conclusion uses the unchanged underlying topological
spaces of thickenings: a covering family of opens on `X` corresponds to a
covering family of lifted opens on `Y`. Expressing this as local surjectivity
of the presheaf coproduct also requires the comparison between open covers
and local lifting of sections on the slice fppf site, using descent for
open immersions. This family, base-change and coverage argument explains the
intended provenance; none of its steps is proved in this statement module.
In particular, Tag 05ZP alone is not cited as asserting the full Lean formula.

## Exact proposition

The declaration is a `def` returning `Prop`, with this body:

```lean
∀ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (i : X ⟶ Y),
  IsThickening (hom i) →
  ∀ (I : Type u) (U : I → Over S)
    (a : ∀ k, (schemeYoneda S).obj (U k) ⟶ X.presheaf),
    (∀ k, IsOpenImmersion (a k)) →
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) (Sigma.desc a) →
    ∃ (V : I → AlgebraicSpace S) (j : ∀ k, V k ⟶ Y)
      (c : ∀ k, (schemeToSpace S).obj (U k) ⟶ V k),
      (∀ k, IsOpenImmersion (hom (j k))) ∧
      (∀ k, IsThickening (hom (c k))) ∧
      (∀ k, IsPullback (a k) (hom (c k)) (hom i) (hom (j k))) ∧
      CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
        (Sigma.desc (fun k => hom (j k)))
```

All geometry is the published geometry from `Basic`, `Thickening` and
`SchemeLocalGeometry`, imported through the latter module. `X`, `Y` and every
`V k` are actual algebraic spaces. Each `U k : Over S` is an actual scheme
over `S`; `schemeYoneda S` is lifted Yoneda with values in `Type (u + 1)`.
Each input `a k` is an actual natural transformation and satisfies the
published representable scheme-test open-immersion predicate.

The existential witnesses are the actual family of spaces `V`, actual
space morphisms `j k : V k ⟶ Y`, and actual space morphisms
`c k : (schemeToSpace S).obj (U k) ⟶ V k`. Their index type remains
the given `I : Type u`; no replacement or refinement of indices occurs.

For each `k`, the top arrow of the square is `a k` and its left arrow is
`hom (c k)`. The right arrow is `hom i` and the bottom arrow is `hom (j k)`.
The top-left corner is the presheaf represented by `U k`, definitionally
the underlying presheaf of `(schemeToSpace S).obj (U k)`. `IsPullback`
asserts the universal property in the actual category of presheaves,
including commutativity.

Both coverage clauses use the actual categorical `Sigma.desc` and
`CategoryTheory.Presheaf.IsLocallySurjective` from Mathlib's
`CategoryTheory.Sites.LocallySurjective`. This means every section over
a test scheme lies locally in the image for the slice fppf topology.
For the coproduct map the local preimage includes a choice of chart.
This differs from the published representable geometric `IsSurjective`.
`IsThickening` retains its existing meaning: representable closed immersion
and geometric surjectivity on scheme tests, with no objectwise
surjectivity requirement on sections.

## Scope

The declaration adds no order bound, affineness, noetherianity, global
quasi-compactness, quasi-separatedness or scheme-representability premise.
The source space `X` need not be a scheme, and the witnesses `V k` are only
required to be algebraic spaces. Their schemeness or affineness, finite
surjective affine descent, scheme-chart gluing and the parent schemeness
theorem remain separate results. This module preserves all prerequisite
and parent target/import pairs.
