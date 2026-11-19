# Degrees of splitting fields for actual local division algebras

Serre, *Local Fields*, Chapter XIII, §3, Corollary 3 uses the degree of
an embedded maximal subfield and divisibility of finite splitting degrees
in the proof of the equality between division degree and Brauer order.
This module implements those two algebraic inputs for the actual classes.

For an embedded field of degree equal to the division degree, the tensor
algebra acts on the division ring by left multiplication by the division
factor and right multiplication by the embedded field. The action is
linear over the embedded field's scalar action. Simplicity gives an
injection into its endomorphism algebra. The two dimensions agree, so the
action is an isomorphism and gives a split matrix chart. The published
local division subfield of full residue degree supplies a field of the
required dimension in every characteristic.

For any finite splitting field, restrict the action on the split matrix
column space to the division algebra. Its dimension over the base is the
splitting degree times the division degree. It is also its dimension as
a division-algebra module times the square of the division degree.
Cancelling gives divisibility. The same result applies to a vanishing
scalar-extended Brauer class by the matrix chart for a neutral class.
Over the ground field itself this rules out a neutral degree-two class.
