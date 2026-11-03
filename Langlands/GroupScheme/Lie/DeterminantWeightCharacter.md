# The determinant as the dimension-weighted sum of actual Lie weights

For an arbitrary field `k`, an automorphic action of `H` on an affine group
scheme `U`, natural finite Lie coordinates `c`, and a morphism `j : T → H`
from a split commutative torus, `lieWeightCharacter` is a character in the
actual integral character lattice of `T`. It sums the character attached to
each index of `lieWeightBasisIndex`. Each nonzero weight space contributes
its dimension many copies of its character. The zero character is included
when its weight space occurs. A zero-dimensional Lie module gives the empty
sum. Neither local finite type nor a monomorphism assumption on `j` is needed.

The finite enumeration uses `finite_lieWeightBasisIndex`, which follows from
the actual split-torus Lie decomposition and finite coordinates. Evaluation
on each affine test algebra turns the sum into the product of the corresponding
character values. Bilinearity computes its integral cocharacter pairing.

If the actual Lie module is nontrivial and every occurring weight has strictly
positive pairing with a given cocharacter, this sum has strictly positive
pairing and is nonzero. Nonemptiness comes from the collected basis of the
nontrivial module. Positivity of individual weights remains an explicit
hypothesis; this module does not construct a positive chamber.

When `H` is affine, `torusCharacterRestrict_determinantCharacter` identifies
this sum with the restriction of the existing algebraic determinant character
`determinantCharacter a c`. Its proof combines the all-affine-test product
formula with `differential_det_lieWeightBasis`. Equality of morphisms follows
by evaluating on the universal affine point of `T` and cancelling the affine
coordinate isomorphism. Thus no rational-point density argument is used.
Strict positivity on a nontrivial Lie module also makes the restricted
determinant nonzero.

If `j` is monic, every rational normalizing point fixes this character sum.
This follows from the determinant identity and the existing invariance of
restrictions of rational characters under the normalizer action. The result
requires no finite normalizer quotient or reductivity assumption.

This is derived internal content: the construction combines the actual weight
basis and determinant formula in `Lie/TorusDeterminant`, the algebraic character
in `Lie/ActionDeterminant`, and the rational-character restriction and fixedness
in `Rational/RelativeWeylRootKernel`, using finite sums and the integral lattice
pairing. It counts weights with multiplicity, unlike the distinct-character
sum in `Rational/NormalizedWeightSum`. It does not supply geometric root
reflections, positive-root containment, field-base-change compatibility, or
the ambient maximal split centralizer theorem.
