# Nagata's theorem in nonzero characteristic

`Langlands.GroupScheme.nagataLinearlyReductive` proves the published
`NagataLinearlyReductiveStatement.{u}`. The theorem applies to every affine
group scheme of finite type over a field of nonzero characteristic. It uses
the all-test finite-coordinate definition of linear reductivity and the
actual identity component, including for nonreduced groups.

For the identity-component necessity, extend the ground field to its
algebraic closure. The published field-extension theorem transfers linear
reductivity by the normalized-integral criterion. Over the algebraic closure,
the proof uses the following Frobenius induction.

- For a reduced ambient group the canonical identity component is reduced.
  Its reduction is smooth and connected. The exclusion of nontrivial connected
  closed unipotent subgroups of the ambient linearly reductive group supplies
  the hypothesis of the smooth torus criterion on this reduction.
- A closed linear embedding of a linearly reductive ambient group has
  multiplicative-type first Frobenius kernel. Its tangent matrices are
  semisimple by the nilpotent tangent obstruction and a separable relation
  constructed from iterated prime powers. The tangent matrices commute and
  admit a common eigenbasis. On the first kernel, each coordinate's
  characteristic power comes from its augmentation. The diagonal entries
  spanning its cotangent have dual Euler derivations. These determine the
  constants and force all off-diagonal entries of the universal matrix to
  vanish in the conjugated representation. The kernel is a closed subgroup
  of the split diagonal torus.
- A common exponent `p ^ r` kills the coordinate nilradical. Each schematic
  Frobenius image retains linear reductivity by injective pullback of
  coefficients. Its nilpotence bound drops by one because its coordinates
  pull back to `p`th powers. The induced map on identity components is an
  fppf quotient. Its kernel is a closed subgroup of the multiplicative-type
  ambient kernel. The multiplicative-type extension theorem with connected
  quotient gives the induction step.

The actual base-change isomorphism for identity components transports the
conclusion to the base change of the original identity component. Over the
algebraic closure this group is diagonalizable with finitely generated
characters. That diagonalization supplies the splitting extension in the
definition of multiplicative type over the original field.

The component-order necessity uses the regular representation of the finite
geometric component quotient. For sufficiency, the multiplicative-type
identity component supplies a stable projection over the algebraic closure.
Averaging over the prime-to-characteristic component quotient gives an
actual ambient-equivariant projection, whose stable kernel is a complement.
The projection descends along the field extension. The three implications
assemble through `nagataLinearlyReductive_of_parts`.

The statement is Milne, *Algebraic Groups*, corrected reprint (2022), Remark
12.56, printed p. 249, with component index as in Proposition 2.37. The
necessity proof follows the Frobenius and tangent route in Demazure–Gabriel,
*Groupes algébriques I* (1970), IV §3, Theorem 3.6 and Lemma 3.7, printed
pp. 509–511. The sufficiency proof uses Milne's stable-complement criterion
and component averaging, Proposition 4.17 and Exercise 4-3.
