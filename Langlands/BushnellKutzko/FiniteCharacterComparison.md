# Comparing families of characters on a finite abelian group

`FiniteCharacterComparisonStatement` concerns additive homomorphisms `a, b` from
an abelian group `X` to `AddChar Y ℂ`, the complex character group of a finite
abelian group `Y`. A character takes addition in `Y` to multiplication in `ℂ`,
and addition of characters is pointwise multiplication. Suppose that every
nonzero `y` in `Y` has `b x y ≠ 1` for some `x` in `X` and that the kernel of `a`
is contained in the kernel of `b`. Then `a` is surjective.

`surjective_of_character_separation` embeds `Y` into the character group of the
image of `b` by evaluation. Finite abelian duality identifies the cardinalities
of a finite group and its character group. The kernel inclusion makes
`a x ↦ b x` a well-defined surjection between the images. Consequently the
target of `a` has cardinality at most that of its image, and the inclusion of
the image into the target is bijective.

This is a finite duality argument for the transitivity on extending characters
used in Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), (8.2.26), printed pp. 287–289. There the cardinality comparison uses
lattice indices. Here the hypotheses isolate the separating character family
and the inclusion of kernels that suffice for the comparison.
