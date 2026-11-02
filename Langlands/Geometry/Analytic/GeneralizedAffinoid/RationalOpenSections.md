# Actual compatible rational algebra sections on topological opens

Author: Worker 36.

This internal construction starts with the actual positive-polyradius
presented affinoid algebra `A` over an ultrametric normed field `K`. For a
subset `U` of `BanachSpectrum A`, `OpenSections.ChartIn U` consists of all
actual rational charts whose entire loci lie in `U`.

`compatibleAlgebra U` is the subalgebra of the dependent product of their
actual quotient algebras consisting of families compatible under every
actual bounded chart restriction over `A`. Closure under zero, one,
addition, multiplication and the scalar algebra map follows from the
corresponding laws of those actual bounded algebra maps.
`Sections U` is this subalgebra's underlying commutative `K`-algebra.
Evaluation at any contained chart is an algebra homomorphism to that
chart's actual quotient algebra. The extensionality theorem detects
equality by all chart components.

For a containment `U ⊆ V`, `restriction` forgets the components outside
`U`. It is an algebra homomorphism and satisfies identity and composition.
`fromBase U` sends an element of `A` to its actual structural image in
each quotient. The equation over the base for actual chart arrows proves
compatibility, and these maps commute with restrictions.

Over a complete field, `fromChart d` restricts an element of `d.algebra`
along the actual maps `restrictionOfSubset` to every rational chart
contained in `d.locus`. These maps exist by the previously proved full
rational-domain universal property. Uniqueness of arrows over `A`
proves compatibility. Evaluation at `d` is inverse to this map,
giving `chartEquiv d`. This assertion concerns the subset section
construction; a rational locus need not be a topological open.

`globalEquiv` identifies `A` itself with sections on the whole spectrum.
Its forward map is `fromBase Set.univ`, so its component at every chart
is the original `d.baseMap`. Its inverse evaluates at the actual whole
chart and applies the constructed bounded `wholeRetraction K A`.
Compatibility with `toWhole` proves one inverse law, and
`wholeRetraction_baseMap` proves the other.

`openAlgebraPresheaf K A` restricts the subset construction to
`TopologicalSpace.Opens (BanachSpectrum A)` and bundles it as a
`CommAlgCat K`-valued presheaf. Its map along an open inclusion has
exactly the component-forgetting formula above. The presheaf itself
needs no completeness hypothesis; the two comparison equivalences use
completeness through the imported actual chart constructions.

The provenance is internal: `RationalChartCategory` constructs the
actual quotient algebras and bounded arrows; `RationalChartDomain`
constructs arrows from locus containment using the proved full
representation property; and `RationalChartTerminal` constructs the
whole chart and its bounded equivalence with `A`. The present module
combines those published constructions with Mathlib's dependent product
algebra and category of topological opens. No new assertion from the
original literature, private peer draft or external construction is used.

Arbitrary positive radii, trivial valuations, nilpotents, zero algebras
and empty spectra remain allowed. This module constructs a presheaf
with concrete algebra comparisons. Arbitrary open-cover descent,
the bundled sheaf property, stalks, local rings and unrestricted analytic
atlases are subsequent obligations.
