# Complete bounded-map separation on refining source charts

Author: Worker 36.

This internal construction proves that restriction to any locally refining
selection of original source charts detects equality of full strong maps.
Its inputs are the actual presented affinoid chart algebras and their original
bounded restrictions. It derives from the existing compact quasinet subcover
and finite full-domain algebra separation constructions; no additional
original-source assertion is invoked.

For an original chart `i`, `FiniteSelectedChartCover` retains a finite list of
selected original charts, their containments in `i`, and coverage of `i`.
`finiteSelectedChartCover` constructs these data: apply the relative local
refinement condition to the singleton family containing `i`, and use the
compactness of its actual spectrum image to collect a finite cover. Index the
result by a finite ordinal. No downward closure or directedness is required.

The cover's `domainCover` represents each selected chart by its original
algebra, structural bounded restriction, and full affinoid-test universal
property. Its target is the actual whole-spectrum domain of the original
algebra at `i`. The cover's restriction maps are exactly the original stored
restrictions, as `domainCover_map_restriction` records.

`algebra_ext_of_refiningSelection` applies the proved finite full-domain
algebra separation theorem to this constructed cover.
`boundedAlgHom_ext_of_refiningSelection` applies it to each input of two
bounded algebra maps. Their source can be any normed commutative algebra over
the coefficient field, with an independent universe and without completeness.
These equalities retain nilpotent information; they are not inferred from
values of multiplicative seminorms.

For strong maps `f` and `g`, equality of their selected-source restrictions
already gives equality of their literal continuous base maps. On an arbitrary
admissible source/target chart pair, compose the two bounded pullbacks with
all selected original restrictions into the source chart. The strong-map
restriction identities identify these composites with the two local
pullbacks, which agree by the supplied equality of restricted strong maps.
Bounded-map separation therefore identifies the full original pullbacks.
`restrictSubatlasSource_injective` follows by strong-map extensionality. The
presentations can be arbitrary, without saturation or downward closure of the
selection.

The existing source-quotient equality criterion says that two original strong
maps become equal precisely when their restrictions agree on some refining
source selection. The newly proved injectivity removes that selection from
the conclusion. `strongFunctor_map_injective` and the faithful instance prove
that the original strong-map functor to the actual quotient is faithful.
`strongHomEmbedding` packages the resulting embedding on complete Hom types.
It does not supply an original strong representative for every quotient arrow.

The coefficient field may be trivially valued. Empty chart spectra and empty
finite covers are allowed. Field, ambient-space and chart-index universes are
independent. Arbitrary quotient matching-family gluing, identification with the
full analytic category, and the etale and equivariant site constructions remain
separate obligations.
