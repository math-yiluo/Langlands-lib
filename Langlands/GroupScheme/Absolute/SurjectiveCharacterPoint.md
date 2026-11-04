# Infinite-order values of a surjective character

For any field `k : Type u`, any group scheme `G` over `Spec k`, and any
rational character `χ : G → Gm` whose underlying scheme morphism is surjective,
`SurjectiveCharacterInfiniteOrderPointStatement.{u}` asserts that an
algebraically closed extension field `K : Type u` and a point `x ∈ G(K)` exist
such that the unit `χ(x)` has infinite multiplicative order: for every nonzero
natural number `n`, its `n`th power differs from `1`.
The Lean expression for this unit is `Lie.characterValue` of the identity
character of `Gm`, evaluated at the point `x ≫ χ`. No commutativity, affineness,
finite type, smoothness or connectedness assumption on `G` is imposed.
`surjectiveCharacterInfiniteOrderPoint` proves the proposition, using the
helper `rationalCharacters.exists_infiniteOrder_point_of_surjective`.

This is an internal generalization of the existing construction in
`CentralSurjectionImage.SurjectiveCharacterPoint` to a possibly noncommutative
source. It uses the same residue-field argument, without any commutative
character-lattice API for `G`. Its imported compositum and polynomial lemmas
remain unchanged.

Take the fraction field `L = k(X)` and its distinguished unit `X`. The
corresponding `L`-point of `Gm` has an underlying scheme point, which lifts to a
point `z` of `G` by surjectivity. The residue field of `z` and the field `L` are
extensions of the residue field at its image in `Gm`. Their tensor product has
a maximal ideal; an algebraic closure of the resulting quotient field is a
common algebraically closed field `K`. The two maps to `K` agree on the common
residue field. Functoriality of the canonical residue-field morphisms therefore
constructs an actual `K`-point `x` whose image under `χ` is the image of `X`.
The proof checks the structure morphism to make `x` a point over `Spec k`.

Naturality of evaluation of the identity character identifies its unit value
with the image of `X` in `K`. An injective field map preserves the inequality
`X^n ≠ 1`, proved from polynomial degrees for each nonzero `n`. This yields the
asserted infinite order in every characteristic, including over finite fields.
This supporting result does not prove the parent no-torus unipotence theorem.
