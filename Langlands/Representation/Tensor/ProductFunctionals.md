# Product functionals on finite tensors

`productFunctional` evaluates a family of factor functionals on a finite algebraic tensor. Its value on an elementary tensor is the product of the factor values. Pullback along a tensor of linear maps pulls back each factor functional. The one-factor slice uses contraction against all the other factor functionals to obtain one vector in the chosen factor. Evaluating the original functional after an operator in that slot is the same as evaluating the chosen functional on the operator applied to this vector.

If the supplied families of functionals separate their factors, `productFunctional_separates` shows that the corresponding product functionals separate the finite tensor. Each family defines an injection into the dual of the free vector space on its index. The Library's injective tensor pairing gives an injection into the dual of the tensor of these free spaces. Vanishing of the product functionals gives vanishing on the tensor basis formed from the single generators, so injectivity forces the tensor to be zero.

`contractRight` applies a functional to the second factor of a binary tensor. It commutes with operators on the first factor. Contractions by the basis-coordinate functionals on the second factor detect every coordinate of a tensor and show that the full algebraic dual separates it.

These are internal linear-algebra lemmas for the coefficient argument of Task 7041. The finite tensor operations use the algebraic tensor products in Mathlib. Their application to restricting to one place is motivated by the finite-support argument of R. P. Langlands, *On the notion of an automorphic representation* (1979), Lemma 1, printed p. 203 (PDF p. 198).
