# Proof of `Langlands.GroupScheme.FiniteHomMaximalTorusReflectionStatement`

This module proves the published proposition `Langlands.GroupScheme.FiniteHomMaximalTorusReflectionStatement` (module `Langlands.GroupScheme.Torus.FiniteHomMaximalityStatement`) at every universe `u`. The statement says that for connected reductive field groups `G`, `H`, a homomorphism `π : G ⟶ H` with finite underlying morphism, a closed torus `j : T ⟶ G`, a maximal torus `i : S ⟶ H` and a homomorphism `f : T ⟶ S` with surjective underlying morphism and `j ≫ π = f ≫ i`, the torus `j` is maximal.

The theorem is `Langlands.GroupScheme.finiteHomMaximalTorusReflection : FiniteHomMaximalTorusReflectionStatement.{u}`, with no hypotheses.

## Proof

The proof term is the published reduction `finiteHomMaximalTorusReflection_of_torusImage`, whose only hypothesis is `TorusImageClosedTorusStatement`, applied to its published proof `torusImageClosedTorusStatement`.

The theorem adds no mathematics; it names a combination of published results.

## Published inputs

- `Langlands.GroupScheme.finiteHomMaximalTorusReflection_of_torusImage` (module `Langlands.GroupScheme.Torus.FiniteHomMaximalityReduction`)
- `Langlands.GroupScheme.torusImageClosedTorusStatement` (module `Langlands.GroupScheme.Torus.ImageProof`)
