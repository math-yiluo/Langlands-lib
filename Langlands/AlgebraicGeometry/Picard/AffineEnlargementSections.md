# Sections on finite stages containing a chosen base

Let `R → A` be an algebra of commutative rings in an arbitrary universe `u`,
and let `B` be an `R`-subalgebra of `A`. The category
`AffineAlgebraStageAbove B` consists of finitely generated `R`-subalgebras
`C` of `A` containing `B`, ordered by inclusion. This module constructs
their actual affine tests and proves a section-colimit theorem with the
canonical restriction maps.

The construction is internal. It combines the published finite-stage order
isomorphism in `AffineStageEnlargement`, the specified-section descent and
affine restriction-injectivity results in `AffineIsomColimit`, and the
ordinary iterated-slice equivalence. It introduces no additional theorem
from the literature.

## The actual tests and comparison maps

The base object `affineBase R B` is `Spec B → Spec R` in the scheme slice.
`affineAlgebraStageAboveTest C` is the canonical map from the `C` test to
this object, regarded as an object of the further slice
`Over (affineBase R B)`. `affineAlgebraStageAboveRestriction C` is the
canonical arrow from the whole `A` test to the `C` test. Both use the
published scheme maps induced by subalgebra inclusions.

`affineAlgebraStageAboveScheme B` is the resulting contravariant system
of tests. Its identity and composition equations are proved by the
corresponding equations for those inclusion maps.

There is another description of the same test: reinterpret `C` as a
`B`-subalgebra of `A` using `subalgebraOver C.property`, take its affine
test over `Spec B`, and apply `iteratedSliceBackward`. The isomorphisms
`affineAlgebraStageAboveBaseIso` and `affineAlgebraStageAboveTestIso`
identify this description with the original test. The first compares the
structure maps to `Spec R`; the second makes the comparison in the further
slice. Their underlying scheme maps are identities. The structure-map
equation follows from contravariant functoriality of `Spec` and the
composite algebra map.

`affineAlgebraStageAboveWholeIso` makes the corresponding identification
at `A`. The lemma `affineAlgebraStageAboveTestIso_restrict` proves that
these identifications commute with the canonical whole-to-stage arrow.
It is an equality of arrows in the iterated slice, proved by two slice
extensionality steps and the identical underlying scheme maps.

## The canonical section colimit

For any functor
`G : (Over (affineBase R B))ᵒᵖ ⥤ Type (u + 1)`,
`affineAlgebraStageAboveSections B G` evaluates `G` on these tests.
`affineAlgebraStageAboveSectionsCocone B G` has vertex `G` evaluated at
the whole `A` test, and its legs are exactly `G` applied contravariantly
to `affineAlgebraStageAboveRestriction`.

`affineAlgebraStageAbovePresheaf B G` pulls `G` back along
`iteratedSliceBackward.op` to a presheaf on the full scheme slice over
`Spec B`. Suppose this presheaf is naturally represented by an affine
scheme locally of finite presentation over `Spec B`.

The lemma `affineAlgebraStageAboveSections_restrict` applies `G` to the
commutative comparison square above. It identifies the canonical
restriction in the original slice with restriction over `B`, including
the two section identifications.
`affineAlgebraStageAboveRestriction_injective` consequently proves that
every original stage-to-whole restriction is injective: transport an
equality to the `B` description, use affine representability to detect
equality after the injective subalgebra extension, and transport it back.
This injectivity assertion does not require that `B` be finitely generated.

If in addition `B.FG`, `exists_affineAlgebraStageAbove_section` descends
each specified whole section to a finite stage containing `B`. It first
transports the section to the `B` description and applies the published
specified-section descent theorem. The resulting finitely generated
`B`-subalgebra determines a finitely generated `R`-subalgebra containing
`B` via `affineAlgebraStageEnlargementOrderIso`. Transporting its section
back and using the comparison square proves the exact original
restriction equality.

`affineAlgebraStageAboveSectionsIsColimit_of_representable` constructs
`IsColimit` for the stated canonical cocone under these two hypotheses.
The enlargement order isomorphism transports filteredness from the finite
`B`-stage category. The proof then uses
`Types.FilteredColimit.isColimitOf'`: the preceding descent theorem gives
joint surjectivity, and restriction injectivity gives the required
eventual equality already at the same stage with its identity arrow.

## Actual Picard isomorphisms

For `f : X → Spec R` and two actual Picard families `L,M` on the base
`affineBase R B`, `PicardGroupoid.affineEnlargementIsomPresheaf` is the
published pseudofunctor's Hom presheaf on the iterated slice, followed
by the usual universe lift. Thus its values are actual isomorphisms of
the ordinary pullbacks of `L,M`; its maps retain the pseudofunctor's
composition comparisons. Its pullback to `Spec B` is definitionally
the published `relativeIsomPresheaf`.

`affineEnlargementIsomSectionsIsColimit` supplies the preceding colimit
when `B.FG` and `f` is proper, flat, and locally of finite presentation.
It discharges affine finite-presentation representability using the
published line-bundle Hom theorem and its Hom-to-Isom implication.
`HasAffineEnlargementIsomSectionsColimit` is the Prop-valued assertion
that the canonical cocone has this universal property, and
`hasAffineEnlargementIsomSectionsColimit` proves it with the same
hypotheses.

All rings and schemes retain arbitrary universe `u`. There is no
Noetherian, field, reducedness, or finite-type assumption on `A`.
This result concerns two fixed families and their section diagram. It
does not construct a category of all finite-stage families, an
equivalence with the groupoid over `A`, or a smooth scheme atlas.
