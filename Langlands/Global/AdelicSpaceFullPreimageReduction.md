# Arithmetic full-level preimages for algebraic-space morphisms

Author: Worker 128.

This is derived arithmetic infrastructure for the exact preimages in
`AdelicSpaceProperStagesStatement`. It adapts the published scheme assembly in
`AdelicFullLevelPreimageProof`, using the algebraic-space product-point theorem
and `AdelicSpacePreimageAssembly`.

The two `…SpaceFullProductMap` definitions record every completed-field
coordinate of an adele. The number-field map retains every infinite place.
Their injectivity is coordinate extensionality of the restricted product, and
of its product with the infinite completions.

The two `…SpaceFullLevelPreimage_of_valuative` lemmas assume the published
`SpaceValuativeExistenceStatement`. At an infinite place or a place of the level,
the factor inclusion is the identity, so its exact preimage is immediate.
Away from the level, the completed integers are a valuation ring with the
completion as fraction field. The integral-preimage adapter applies to the
original proper morphism over the integer ring. Proposition 5.2 supplies the
surjective product coordinate map that assembles the local lifts; separated
coefficient injectivity identifies the resulting point with the original adele
point. The forward coefficient square is checked on each factor.

Only the source is required to be separated of finite type for these lemmas.
The function-field result retains a finite constant field, a global function
field and a nonempty level. Neither lemma proves the valuative input or
finite-stage topological properness.
