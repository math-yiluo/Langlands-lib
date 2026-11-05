# A category with the actual source-subatlas Hom quotients

This internal construction uses the actual saturated atlas localization,
the proved source Hom equivalence, and the constructed Ore composition and
source normalization. These are imported from the preceding `Saturated*`
modules. No new original-literature assertion is attributed here. The
comparison and localization properties are derived from those constructions;
neither a category equivalence nor a localization property is geometric input.

## Objects, universes and complete numerators

The field `K : Type u` is complete, normed and ultrametric. The independent
universes `u`, `v` and `w` remain those of
`SaturatedAtlasPresentation.{u,v,w} K`: the objects retain their literal
ambient spaces, original atlas charts, actual affinoid algebras and full
local-domain closure.

For two such objects, the imported `SourceHomQuotient A B` is the quotient
of pairs consisting of an actual refining original-chart selection `P`
and a complete strong numerator `A.refiningSubpresentation P ⟶ B`.
Its relation is full strong-map equality after restriction to a common
refining selection. In particular, it compares all admissible bounded
algebra pullbacks, as well as the continuous map.
The imported `sourceHomEquiv` is a proved bijection between this quotient
and the existing path-localization Hom type.

`SourceCategory` is a separate object type alias for these actual
presentations, with `ofPresentation` and `toPresentation` inverse by
definition. Its category instance has exactly `SourceHomQuotient` as its
Homs, in `Type (max u v w)`. The alias separates this category instance from
the original strong-map category without replacing any object data.

## Identity, composition and representatives

`sourceHomId A` is the inverse image of the localized identity under
`sourceHomEquiv`. `sourceHomComp f g` is the inverse image of the composite
of their images. The equations `sourceHomEquiv_id` and
`sourceHomEquiv_comp` follow from the inverse law of the proved
equivalence. Applying its injectivity then reduces the two unit laws and
associativity to the corresponding laws in the existing localization.
These operations and proofs form the category instance.

The construction also identifies the operations on actual representatives.
`sourceHomOfFraction φ` uses the constructed original-source selection
`fractionSourceSelection φ` and the complete strong numerator
`fractionSourceReverse φ ≫ φ.f`. The source-normalization theorem proves
that its image is exactly `localizedRightFraction φ`.

For representatives with numerators `f` on a selection of `A` and `g`
on a selection of `B`, `sourceHomComp_ι` identifies their composite with
`sourceHomOfFraction` applied to the actual `rightFractionComp` of their
source-refinement fractions. Thus composition has a representative obtained
by the previously constructed Ore square, followed by normalization to a
subatlas of the original source. The proof applies injectivity of
`sourceHomEquiv`, its component and composition formulas, normalization,
and the proved localized Ore-composition equation. It does not assume
that the two original numerators are directly composable.

## Comparison and the localization universal property

`comparisonFunctor` sends an object to its image in the existing
localization and sends an arrow by `sourceHomEquiv`. The two displayed
operation equations prove functoriality. The bijection proves fullness and
faithfulness. The existing `localizedObjectEquiv` shows surjectivity on
objects, by taking `ofPresentation` of its preimage. This supplies essential
surjectivity and hence constructs `localizationEquivalence`.
Here faithfulness concerns this comparison functor, not the original
strong-map localization functor.

`strongFunctor` sends an original complete strong map to the inverse image
of its localized arrow. Its identity and composition laws follow by
applying the injective Hom comparison, the two operation formulas and
functoriality of the original localization. Applying the Hom inverse law
on each arrow proves the strict equality
`strongFunctor ⋙ comparisonFunctor = localizationFunctor`; the objects
already agree by definition.

`localizationFunctor_inverseComparison` is an explicit natural isomorphism
from the original localization followed by the inverse equivalence to
`strongFunctor`. It is assembled by whiskering the preceding strict
comparison, applying the functor associator, and then using the unit of
`localizationEquivalence` and the right unitor. Transport of localization
along this constructed equivalence proves the `IsLocalization` instance
for `strongFunctor` at the original full quasi-isomorphism property.

`functorEquivalence D` consequently gives the equivalence between functors
out of `SourceCategory` and original strong-map functors that invert those
quasi-isomorphisms. It includes natural transformations through Mathlib's
localization universal property. The target category has its own object
and morphism universes; they are not identified with `u`, `v` or `w`.

## Original arrows and literal continuous maps

For every refining selection `P`, `strongFunctor_map_eq_ι` represents the
image of an original map `f : A ⟶ B` by the actual restricted numerator
`A.refiningSubatlasInclusion P ≫ f`. After applying the injective
comparison, the fraction formula reduces the assertion to functoriality
and cancellation of the inverse inclusion isomorphism with its forward
map. In particular, `id_eq_ι` represents the identity by the actual
inclusion on every such source selection. Its proof specializes the
original-map formula to an identity and uses the right unit law.

`SourceCategory.spaceFunctor` is `comparisonFunctor` followed by the
existing descended literal-space functor. On objects it is exactly the
original ambient topological space. `spaceFunctor_map_ι` sends the class
of any complete numerator `f` to `TopCat.ofHom f.baseMap`, by the
previously proved same-space fraction formula.
`spaceFunctor_map_strong` specializes this to every original strong map
using the Hom inverse law. The strict equality
`strongFunctor_spaceFunctor` follows from the strict category comparison
and the original localization's space-factorization equality.

Finally, `localizedCategory_locallySmall` transports the small Hom
property of `SourceCategory` along the constructed equivalence. Thus the
larger path model is locally small at `max u v w`, with the explicit
original-source quotient providing the size bound.

## Scope

This unit supplies the category with actual source-subatlas quotient Homs,
its representative operations, comparison equivalence, localization
universal property and literal-space formulas. It does not assert
injectivity of source restrictions or faithfulness of `strongFunctor`.
Identification with a separately specified full analytic-space category,
actual analytic etale and quasi-etale morphisms and sites, equivariant
sites, compact/distinguished domains and Harris tower specializations
remain obligations of the surrounding task. Every predecessor retains
its independent acceptance and publication gate.
