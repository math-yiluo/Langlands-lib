# Reflection of Cartan generation through finite surjections

This is an internal derived result for the proof of Cartan generation. Its
provenance is the Library's smooth generated-family theorem, schematic image
theorem, torus maximality reflection, torus centralizer transport, and integral
finite-map rigidity. It is not a transcription of a literature statement.

`FiniteHomCartanGenerationReflectionStatement` says the following over any field
in any universe. Let `q : G → H` be a finite surjective homomorphism, with `G`
smooth, connected and affine, and `H` smooth and affine. Assume that every
maximal torus `s : S → H` has a closed torus lift `t : T → G` and a surjective
homomorphism `f : T → S` satisfying `t ≫ q = f ≫ s`. If every closed subgroup
of `H` containing all its Cartan subgroups has full range on all test schemes,
the same holds for `G`. No infinitude or perfectness of the field is assumed.
Closed competitors may be nonsmooth and nonreduced.

The theorem `isGeneratedByCartanSubgroups_of_finiteHom` implements this statement.
It first constructs the smooth connected affine closed subgroup `D` generated
by all actual Cartan subgroups of `G`. Their smoothness and connectedness follow
from the torus-centralizer theorems. The schematic image `E` of `D → H` is
again a smooth connected affine closed subgroup, and `D → E` is surjective.

For any target Cartan subgroup, lift its witnessing maximal torus. Finite-map
maximality reflection makes the lifted torus maximal in `G`. Its centralizer
is a source Cartan subgroup and thus factors through `D`. Finite-surjective
centralizer transport shows that `E` contains the chosen target Cartan. Target
generation therefore gives full range for `E → H`. Applying this full-range
identity to the universal point gives a section of `E → H`, hence surjectivity
on the underlying spaces. Consequently `D → H` is surjective and schematically
dominant, since `H` is reduced.

The smooth connected affine group `G` is integral. Integral finite-map rigidity
applied to `D → G → H` makes the closed immersion `D → G` an isomorphism.
Minimality of the generated-family construction against arbitrary closed
competitors now proves the required all-test full-range identity.

`finiteHomCartanGenerationReflectionStatement` proves the proposition-valued
statement. The corollary `isGeneratedByCartanSubgroups_of_isogeny` accepts the
stronger all-torus lifting premise with isogenies supplied by the semisimple
isogeny reduction interface, and uses only the finiteness and surjectivity
parts of these isogenies.
