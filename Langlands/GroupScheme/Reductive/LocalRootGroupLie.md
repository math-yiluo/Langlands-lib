# The actual Lie line of a dynamic root group over a ring

This internal module derives the global root Lie comparison needed in
Task 6700 from the actual dynamic Lie and homogeneous root-group interfaces.
No new external source assertion is used.

Finite-module Nakayama detects zero modules and surjectivity from maximal
residue tensor fibres. Restriction of the root character to the chosen
centralizing cocharacter is trivial and to the contracting cocharacter is
positive. The dynamic weight lifts therefore lift its actual ambient weight
space to the actual root-group Lie module. The composite with the ambient
inclusion differential is the original weight inclusion.

The chosen ambient weight projection retracts the lifted weight inclusion.
Thus the lift is a split injection, and remains injective after any scalar
extension. Smoothness makes the actual root-group Lie module finite and gives
the actual Lie scalar-extension equivalence. An isomorphism of each field
fibre with the additive group makes every field-extended Lie module
one-dimensional. The supplied linear trivialization of the ambient root
weight makes its field extension one-dimensional as well. The scalar-extended
lift is therefore surjective on every maximal residue field. The finite-module
criterion then proves surjectivity over the original ring.

`rootWeightLieEquiv` packages this actual differential lift as a linear
equivalence from the ambient exponent weight to the root-group Lie module.
It retains the character's vanishing dot product with the centralizing
cocharacter, its positive integral dot product with the contracting
cocharacter, the explicit ambient weight trivialization, and actual
additive-group isomorphisms on all same-universe field fibres. Smoothness and
affineness are hypotheses on the original ambient group; the dynamic
representatives inherit the needed properties from the published interfaces.
No connectedness, reducedness, localness, field or nontriviality hypothesis is
placed on the base ring.

The module's finite-module helper proves that a split injection between finite
modules is bijective when their maximal residue tensor dimensions agree. Its
proof applies the preceding surjectivity criterion after tensoring the split
identity, using finite-dimensional linear algebra on each residue field.

These are supplied-data constructions. Constructing field fibre isomorphisms
from the reductive root datum, identifying the coordinate degree with the
cotangent module in the chosen root-group presentation, and building global
root parametrizations remain separate steps of the host task.
