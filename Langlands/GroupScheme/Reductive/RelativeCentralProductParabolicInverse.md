# Relative parabolic extension data

This internal construction records an ambient relative parabolic together with the exact equality between its inverse image in a supplied factor and a prescribed subgroup, on every test scheme. The base scheme is arbitrary.

`RelativeExtension.ofDynamic` takes a cocharacter of a closed factor presenting the prescribed subgroup. It represents the composite cocharacter's ambient dynamic parabolic and applies the published relative dynamic theorem for parabolicity. Reflection of orbit extensions through a closed immersion proves the inverse-image equality. This construction needs ambient reductivity and closedness of the factor, without a global central product hypothesis.

The data pull back along arbitrary morphisms of bases and transport through commuting isomorphisms of the ambient group, factor and prescribed subgroup. The base-change proof uses the point equivalence to show that subgroup inverse images commute with base change. The transport proof uses inverse isomorphisms and the two commuting squares. `intersection_range` identifies the inverse-image equality with the range of the actual scheme-theoretic intersection's first projection.

If central multiplication from a supplied central group and the factor is a central isogeny, `range_unique` proves that any two extensions have equal all-test ambient ranges. It applies the published central-product restriction to both parabolics and then the existing injectivity theorem. Neither uniqueness nor the data assumes the full derived-group correspondence.

The provenance is internal: the construction composes published dynamic representability, relative dynamic parabolicity, closed-subgroup reflection, actual intersection, base-change, central-isogeny restriction and subgroup injectivity interfaces. This module prepares descent; it does not assert existence of an extension for every relative parabolic (constructed in `RelativeCentralProductParabolicDescent`) or the full derived-group correspondence `ReductiveDerivedTorusParabolicCorrespondenceStatement`, which the Library proves as `reductiveDerivedTorusParabolicCorrespondence` in `DerivedTorusParabolicCorrespondenceProof`.
