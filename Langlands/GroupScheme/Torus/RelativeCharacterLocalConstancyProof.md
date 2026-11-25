# Actual characters form an étale local system

`Langlands.GroupScheme.relativeCharacterLocalConstancy` proves
`RelativeCharacterLocalConstancyStatement.{u}`. The relative Hom sheaf
theorem gives étale descent for the actual characters. The étale
diagonalizing cover from `multiplicativeTypeQuasiIsotrivial` supplies
a diagonalizable base change on each member. By the forward direction
of `relativeCharacterConstancy`, the characters there are constant with
finitely generated coefficients. The Cartier base-change isomorphism
identifies those characters with the restriction of the original
presheaf. These data give the required locally constant étale sheaf.

This is the passage from a group of multiplicative type to its
character sheaf in Brian Conrad's *Reductive group schemes* (2014),
Proposition B.3.4, pp. 290–292.
