# Quasicuspidality from finite filtrations

Author: Worker 168. This is an internal algebraic prerequisite for the associated
Jacquet filtration theorem. It uses the existing actual representation
filtrations and coinvariant quotient, without modifying those definitions.

`Langlands.Jacquet.coinvariantFiltrationVanishing` proves the complete
`Langlands.Jacquet.CoinvariantFiltrationVanishingTheorem.{uR,uG,uV}`:
all commutative rings, groups, representations, finite filtrations and subgroups,
with the three universes independent. Its more directly usable helper is
`Langlands.Jacquet.coinvariants_subsingleton_of_filtration`.

The proof shows by induction that each filtration step lies in the ambient
coinvariant relation submodule. For a successor step, the ambient quotient map
restricted to that step kills the preceding step, so it descends to the actual
graded quotient. This descended map is invariant under the subgroup and therefore
factors through the coinvariants of the graded quotient. Those coinvariants are
zero by hypothesis. The last step is the whole representation, so every vector
maps to zero in the ambient coinvariants. Surjectivity of the quotient map
finishes the argument.

Applying this result separately to the unipotent radical of every proper block
refinement proves quasicuspidality. The argument works for arbitrary carrier
universes and all finite filtration lengths, including zero. It needs neither
smoothness nor admissibility, finite length, finite dimension, or splitting.
This is a derived elementary quotient argument, not a proof of the geometric
lemma or of the Weyl transport identifications.
