# Scheme representability from locally surjective open charts

Author: Worker 208. Workers 133 and 336 supplied the interface design in the
task specification.

This module defines the proposition
`Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartGluingStatement`.
It supplies a statement for a later proof; it contains no gluing proof.

## Original source and provenance

The original source is the Stacks Project, Chapter 26, Section 26.15,
[Lemma 26.15.4, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ).
The retained source is registered as
`stacks-open-chart-representability-2026-11-01`, with directory SHA-256
`51771f7545361ce0b0f4f3ebe79f53f862d299ecc08344f3273aeb9a8dc84201`.
The files are `01JJ.html` and the reading aid `01JJ.txt` in
`literature/Stacks Project - Open chart representability (HTML snapshot 2026-11-01)`.
The full original statement, proof and comments were read.

The source considers a set-valued contravariant functor on schemes. It assumes
the Zariski sheaf condition and a covering family of representable subfunctors
whose inclusions are representable by open immersions. Its conclusion is
representability by a scheme. The proof constructs open overlaps between the
representing charts, glues the charts using their canonical overlap
isomorphisms, and applies the sheaf condition to identify the resulting functor
of points with the given functor.

The retained comments include comment 8428, which identifies a restriction
notation typo and explains agreement of the chart maps on overlaps, and comment
9053, which records that the typo was corrected. The current original page was
also checked on 1 November 2026 and displays those two comments. No
source-specific errata note was found in the checked project, current Library
or workspace locations.

The Lean proposition is an **internal adaptation** of this absolute Zariski
criterion. Its precise slice-fppf and lifted-value formula was specified for
the general-thickening consumer by Workers 133 and 336. It is not a verbatim
statement of Tag 01JJ, and this module establishes no comparison theorem
between the two formulations.

## Exact statement

At every universe `u`, the proposition is

```lean
∀ (S : Scheme.{u}) (F : FppfSheaf S) (I : Type u)
  (U : I → Over S)
  (a : ∀ k, (schemeYoneda S).obj (U k) ⟶ F.obj),
  (∀ k, IsOpenImmersion (a k)) →
  CategoryTheory.Presheaf.IsLocallySurjective
    (fppfTopology S) (Sigma.desc a) →
  ∃ V : Over S, Nonempty ((schemeYoneda S).obj V ≅ F.obj)
```

`S` is any actual scheme. `FppfSheaf S` is the published category of actual
sheaves on `Over S` for `Scheme.fppfTopology.over S`, with values in
`Type (u + 1)`. Thus the sheaf condition is part of the input object `F`.
The statement does not require `F` to carry an algebraic-space structure or
to have a prior scheme representation.

`I : Type u` indexes actual schemes over `S`, namely `U k : Over S`.
Each `a k` is an actual natural transformation from the lifted functor of
points of `U k` to `F.obj`. The existing `schemeYoneda S` is
`CategoryTheory.uliftYoneda.{u + 1}`. At a test scheme `T : Over S`, the
chart presheaf has value `ULift.{u + 1} (T ⟶ U k)`.
All test schemes, chart schemes and the base remain in `Scheme.{u}`.
There is no replacement by a presheaf with smaller values.

`IsOpenImmersion (a k)` is the published relative representable
open-immersion predicate from `SchemeLocalGeometry`. It includes
representability of `a k`; for every represented pullback along a map from
an actual test scheme over `S`, its actual scheme projection is an open
immersion. The predicate uses the pullback universal property and tests every
represented square. These are the actual represented open charts intended
by the source's open subfunctors.

`Sigma.desc a` is the actual coproduct map in the presheaf category, from the
coproduct of the chart presheaves to `F.obj`. Here
`CategoryTheory.Presheaf.IsLocallySurjective` is Mathlib's site predicate:
for each test object `T` and section of `F` over `T`, the sieve of maps to
`T` on which the restricted section lies in the image of this coproduct map
is covering for `fppfTopology S`. This hypothesis expresses local chart
coverage. It is distinct from the published geometric-surjectivity
predicate `IsSurjective`, which tests surjectivity of actual represented
scheme projections. The statement keeps precisely the local-surjectivity
hypothesis on the coproduct.

The conclusion provides an actual `V : Over S` and an actual natural
isomorphism `(schemeYoneda S).obj V ≅ F.obj`, wrapped in `Nonempty` so that
the whole assertion is a proposition. The structure map of `V` and its
functor of points retain the base `S`.

## Adaptation and remaining proof obligations

The intended adaptation keeps the source's three ingredients: a sheaf,
actual representable open charts, and local chart coverage. A proof must
use that fppf sheaf data restricts to Zariski sheaf data. For a section over
a test scheme, its pullbacks to the represented charts are actual open
subschemes. Local surjectivity of the coproduct is intended to force those
opens to cover the test scheme: their union contains the images of the
fppf-local lifts. Establishing this passage from the given covering sieve
to a Zariski open cover is a proof obligation.

The overlaps and chart maps must then be glued compatibly with their maps
to `S`, producing an object of `Over S`. The resulting representing
isomorphism must be constructed in the actual lifted-value presheaf
category. These slice, topology and universe compatibilities are also
obligations of a separate proof successor, rather than consequences proved
in this statement module.

The module imports the published `Basic`, `Thickening` and
`SchemeLocalGeometry` interfaces unchanged, and Mathlib's
`CategoryTheory.Sites.LocallySurjective` API. Mathlib is pinned at commit
`5ed2965256430c3649e86755f9576b54eca72435` in the prepared environment.
The absolute ordinary-Yoneda local-representability theorem does not by
itself establish this slice-fppf, lifted-value statement.

The proposition imposes no affineness, noetherianity, finiteness,
quasi-compactness, quasi-separatedness or prior scheme-representability
assumption. It states no thickening, affine descent, open-lifting, Picard
deformation or actual-family comparison result.
