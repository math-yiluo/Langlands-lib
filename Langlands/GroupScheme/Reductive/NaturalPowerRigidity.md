# Prescribed-power rigidity over arbitrary coefficient rings

This internal derived helper generalizes the Laurent substitution argument of
`LocalRootParametrizationRigidity` from degree one to any specified natural
degree `q`. It works over every commutative coefficient ring, including rings
with nilpotents and the zero ring. Its conclusions concern natural operations
on all coefficient algebras and equality of actual additive-group morphisms.

`NaturalLine.Operation.HasLaurentPower F d q` records the single identity
`F(T^d) = T^(d*q) C(F_R(1))` over the Laurent polynomial algebra.
For positive `d`, `eq_mul_pow_of_laurent` proves
`F_A(a) = algebraMap(F_R(1)) * a^q` on every algebra `A`.
The proof evaluates the universal polynomial `F_(R[X])(X)` at `T^d`,
uses the existing injectivity of that substitution, and then evaluates at
`a`. No additivity or restriction on `q` is used. In particular `q` is not
asserted to be a characteristic power. `eq_of_laurent_value_one` consequently
compares operations with the same `d`, `q` and value at one.

`isUnit_value_one_of_fields` proves that the value at one over the base is a
unit if the value at one is nonzero over every field algebra. A hypothetical
nonunit lies in a maximal ideal. Naturality identifies its image in that
residue field with the operation's value at one, giving a contradiction.
Field tests are used only for invertibility of a coefficient, never to detect
equality over the base.

`LocalSplitCell.scalarOperation_ext` tests two additive-group maps over the
coordinate algebra of the source additive group, at the scalar point
corresponding to the identity morphism. Equality of coefficient operations
there yields equality of actual morphisms.
`scalarOperation_comp_scaleHom` computes the operation of postcomposition
with a scaling map.

`hasLaurentPower_of_weight` starts with an all-test character-equivariance
identity whose output weight is the `q`-th power of the input weight. A
supplied cocharacter pairs with the input character to the natural number
`d`. Evaluating at its Laurent torus point and parameter one proves
`HasLaurentPower d q`. Positivity of `d` is needed only when subsequently
applying `eq_mul_pow_of_laurent`.

`existsUnique_unit_scale_of_power` compares two additive-group maps already
known to have the same power degree and unit coefficients `c` and `c'`.
The ratio `c * (c')^-1` gives the required postcomposition scaling on every
algebra. The preceding extensionality result gives equality of actual maps.
Evaluation at one over the base proves uniqueness of the scaling unit.

These are polynomial and coordinate-comparison results. They do not prove
that an ambient isogeny carries one actual root subgroup into another,
derive the character or exponent correspondence of an isogeny, or establish
compatibility with opposite-root duality or Weyl representatives. Those
structural inputs and the final torus-conjugacy theorem remain separate.
