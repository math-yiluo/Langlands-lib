# The actual same-character signed dual model and its block transport

This internal construction combines the published first dual model, change of
additive character by the alternating diagonal, and explicit signed Weyl
identities. It does not assume a model equivalence or a functional equation.

`rankOneSignedDualFunction` sends a function `W` to
`g ↦ W(w_signed inverseTranspose(g) E)`, where `E` negates the leading
coordinate. The actual signed Weyl and `E` are fixed by inverse transpose.
Consequently this is the two-sided translate of the inverse-transpose function
by those exact elements.

`rankOneSignedDualFunctional` applies the inverse of the existing character
change equivalence to the first dual functional. Its character is the original
`psi`, and its representation is the actual inverse-transpose pullback of the
original representation. Evaluating it amounts to translating the original
functional by the signed long Weyl element. The coefficient identity includes
the right translation of the vector by `E`. Surjectivity onto the original
coefficient image therefore realizes the signed dual of every original model
vector in this actual same-character model.

At the complementary block, the published signed-Weyl transport and alternating
block identity turn this signed function into the Library's unsigned long-Weyl
dual with its true block-Weyl right translate, after alternating row signs in
the rectangular variable. The integral and integrability lemmas apply the
published measure-preserving rectangular sign involution and the identity on
the scalar group. They preserve the exact supplied additive Haar measure and
any s-finite measure on the scalar group. No scalar, Jacobian or character
factor is introduced. These lemmas concern the scalar-group product measure;
the previously published quotient-sign result handles compatible quotient
measures separately.

The module supplies algebraic realization and measure transport. It does not
claim convergence or the final matrix functional-equation comparison.
