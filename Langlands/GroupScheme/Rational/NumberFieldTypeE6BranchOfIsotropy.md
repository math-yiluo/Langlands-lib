# The distinguished short-arm vertex from E₆ isotropy

`NumberFieldTypeE6BranchOfIsotropyStatement` derives the totally complex E₆ short-arm marking from `NumberFieldTotallyComplexTypeE6IsotropyStatement`. The marking concerns the actual Tits index of each affine locally finite-type simply connected absolutely almost-simple group of type E₆. Vertex `1` is the endpoint of the short arm, Bourbaki α₂.

Isotropy implies that the index has a distinguished vertex, because the number of distinguished star orbits is the split rank. If the short-arm endpoint is unmarked, `typeE6UnmarkedBranchMarking` forces the distinguished set to be exactly the two long-arm endpoints. `typeE6EndpointKernel` then identifies the actual anisotropic kernel as a simply connected absolutely almost-simple D₄ group with fixed nonfork vertices and zero vector Tits obstruction. `numberFieldTotallyComplexTypeD4VectorIsotropy` gives positive split rank for that kernel, contradicting its anisotropy.

`TitsIndexData.typeE6Branch_distinguished_of_not_isAnisotropic` uses
isotropy of the given group. This form supplies the marking for any
individual isotropic pure twist with the E₆ Cartan matrix.

The argument formalizes the exclusion of the D₄ kernel in Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.8, around diagrams (6.53) and (6.57), and the totally imaginary outer E₆ application on printed p. 385.
