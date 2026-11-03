# Generated-image factors across a schematically dominant source

This is an internal universal-property construction for actual schemes over an
arbitrary base and universe. It builds on `ImageGenerationDominant` and
`ImageGenerationActions`.

Let `p : V ⟶ W` be schematically dominant and `f : W ⟶ G.X` an actual morphism.
For a representative `D : GeneratedImage (p ≫ f)`, the closed immersion of
`D.group` into `G` allows its source factor to descend to a morphism
`D.sourceFactor p f : W ⟶ D.group.X`. The proof applies the published descent
lemma `exists_over_factor_of_schematic_precomp`. Its composite with the ambient
inclusion is `f`; its precomposition with `p` is the original `D.factor`, by
monicity of the inclusion.

The module constructs the coordinatewise morphism between actual finite powers
and proves compatibility with ordered multiplication. Therefore every original
power `D.powerMap n` factors through the corresponding power of `W` and ordered
multiplication of `D.sourceFactor p f`. If the original power is dominant, the
descended ordered power is dominant. This implication uses only dominance of a
composite, with no separability or geometric regularity of `W`.

A point of `W` mapping to the ambient identity maps to the generated identity.
If the fixed envelope is stable under an actual automorphic action and `f` is
equivariant, the descended factor is equivariant for the existing restricted
action on `D.group`. Both claims follow by canceling its monomorphic inclusion.
All equivariance statements and morphism equations retain every test scheme.

This module assumes a representative `D`. It does not assert its existence,
smoothness, connectedness, or a dominant positive power; it only transports an
already given power. In particular it does not prove the general pointed-image
generation theorem or the semigroup commutator bound.
