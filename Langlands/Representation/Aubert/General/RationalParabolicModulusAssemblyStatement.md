# Structural inputs for the actual rational-parabolic modulus target

`RationalParabolicModulusAssemblyStatement` is an internal proposition in
arbitrary universe `u`. It states that the following seven proposition targets
imply the exact original `RationalParabolicModulusStatement`:

- `IwahoriHaarProductStatement`;
- `RationalOppositeHaarReciprocityStatement`;
- `GenericCentralizerStatement`;
- `JointSpecialCompactBasisExistenceStatement`;
- `FiniteCoverCharacterStatement`;
- `ModularCharacterRegularityStatement`;
- `DynamicCentralizerReductiveStatement`.

Each is an explicit premise. This reduction supplies no proof of those targets.
The resulting ambient and parabolic conclusions retain precisely the original
statement's local-field, connected-reductive, canonical-topology,
local-compactness, nonarchimedean, Hausdorff, standard-cocharacter, closedness
and continuous-projection premises.

For ambient unimodularity, use an actual maximal split torus and a generic
cocharacter, whose existence is already proved. The joint-existence input
constructs a common geometric special compact subgroup with both the actual
simultaneous basis and Cartan comparison. The torus modular reduction uses
the first three inputs to trivialize the ambient modular character on that
torus. The actual Cartan section gives a finite `K * torus * E * K` cover.
Regularity trivializes the character on the compact subgroup; the finite-cover
character theorem then gives triviality everywhere.

Apply the same ambient conclusion to the existing standard Levi
representatives, whose connected reductivity follows from the explicit
dynamic-centralizer input and the original standard-cocharacter premise.
The literal-Levi transport and parabolic semidirect reduction then give the
original modulus comparison.

This formulation is derived internally from the stated structural interfaces
and the original target. Its companion `RationalCartanFiniteCover` proves the
finite product-cover step for supplied actual comparison data. General basis
and Cartan existence, opposite reciprocity, centralizer reductivity, and the
unconditional original target remain separate proof obligations.
