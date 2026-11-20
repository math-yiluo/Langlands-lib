# Operator stability of the block constant terms of GLₙ

`finiteSmoothBlockConstantTerm` transports the normalized integral to the
original finite-smooth rational-invariant function space on `GL_n`. Its kernel
is stable for the concrete operator algebra of finite adelic translations,
archimedean compact translations, and enveloping derivatives.

The integral commutes with right translations by associativity of adelic
multiplication. For a real Lie direction, the derivative of the translated
integral is obtained by differentiating the finite-smooth integrand. Joint
continuity of this derivative and compactness of the unipotent quotient
supply the domination on a neighborhood of each parameter. A function in
the kernel therefore has its first Lie derivative in the kernel. Complex
linearity extends this to the complexified Lie algebra, and induction in the
enveloping algebra proves stability for every differential operator. The
concrete operator generators then give `blockConstantTermKernel`.

This derived stability result is the operator-invariance needed to apply the
kernel filtration to the block terms in Langlands's proof of Proposition 2,
printed p. 204, Lemma 4 and the final paragraph (Corvallis Part I, PDF p. 199).
The registered source is `langlands-1979-notion-automorphic-representation`,
SHA-256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
