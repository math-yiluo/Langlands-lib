# Finite products of general linear and multiplicative group schemes

This internal construction combines the published `GeneralLinear`, `Products`, and `Multiplicative` modules. For a natural number n, a finite type I, and a commutative ring R, `GeneralLinearProduct.groupScheme` is the categorical product of one GL_n over Spec R for each element of I, followed by a binary product with Gm over Spec R. It is an actual group scheme, including when I is empty or n is zero.

For every test scheme T over Spec R, `pointsEquiv` constructs a multiplicative equivalence from its points to a family indexed by I of invertible n-by-n matrices over the global sections of T, together with one unit in those global sections. The construction composes the binary-product and finite-product point equivalences with the established GL_n and Gm equivalences. `pointsEquiv_apply` records these coordinates explicitly.

`pointsEquiv_naturality` states that precomposition with a test-scheme morphism applies pullback of global sections to each matrix entry and to the scalar unit. Its proof uses binary-product naturality, then finite-product naturality, then the GL_n and Gm naturality lemmas. No choice of affine test scheme is needed.

This module provides the target for subsequent complex unitary group comparisons. It makes no smoothness, reductivity, or Harris-specific comparison claim.
