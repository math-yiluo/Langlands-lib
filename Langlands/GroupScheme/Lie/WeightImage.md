# Nonzero character weights in actual subgroup Lie images

`Langlands.GroupScheme.Lie.MeetsWeightSpace j i α` packages a nonzero vector
of the ambient character weight space `weightSpace j α` together with an
actual dual-number Lie-kernel preimage under the group-scheme morphism `i`.
The base is any `CommRingCat.{u}`, the acting group is a commutative group
scheme, and only the ambient group is required to be affine.

The definition is an internal abbreviation of the exact existential witnesses
in `Langlands.GroupScheme.RankOneSolvableObstructionStatement`. It makes no
claim that such vectors exist, that the acting group is a torus, or that the
morphisms are subgroup inclusions.

`MeetsWeightSpace.of_factorization` transports a witness along an actual
factorization `f ≫ b = i`. It keeps the ambient nonzero vector and its weight
unchanged, and replaces its Lie-kernel preimage `Y` by `Lie.targetMap f R Y`.
Associativity of composition and the given factorization prove the required
equality of dual-number points. `MeetsWeightSpace.comp` is the composition
special case. These proofs require no injectivity, smoothness or field
hypothesis.

The accompanying module
`Langlands.GroupScheme.Absolute.RankOneSolvableReduction` applies this
transport to Borel containment. These are internal definitions and formal
reductions; they do not establish the geometric rank-one obstruction.
