# Full functional dual and nondegeneracy of finite normalized products

Worker 1732. This is a derived composition of the full top-derivative tensor
comparison and the full Whittaker-functional/top-derivative dual comparison.
It introduces no literature assertion or classification hypothesis.

For arbitrary independent field and representation universes, let `F` be a
finite p-adic extension with compatible topology `T`, and let `psi` be a
continuous nontrivial unitary additive character. Fix any natural ambient rank
`n`, any positive-block shape `B : BlockShape n`, and the actual original
smooth complex factors `sigma i` with carriers in `Type (max uF uV)`.

`finiteProductFunctionalsDualEquiv` identifies the entire upper-unipotent
functional submodule of the actual finite normalized induction with the
algebraic dual of the finite tensor product of the entire top derivatives of
these original factors. It first uses `functionalsTopDerivativeDualEquiv`.
Then it pulls dual functionals back along the inverse of
`finiteProductTopDerivativeTensorEquiv`. Both maps are full complex-linear
equivalences with inverses. No identification of a dual tensor with a tensor
of duals is asserted, and no finite-dimensionality condition is used.

`hasFunctional_finiteProduct_iff` says that this actual normalized product has
a nonzero upper-character functional if and only if every original factor
does. The proof uses `hasFunctional_iff_nontrivial_topDerivative` on the
product and on each factor, with
`nontrivial_finiteProductTopDerivative_iff` in between. This includes the
empty product in rank zero: the factor condition is vacuous and the product
has the scalar-line functional. Singleton products and rank one are included.
`hasStandardFunctional_finiteProduct_iff` specializes the ambient character
at rank `n+1` to the published standard character using their exact equality;
the factor side retains the supplied block ranks and entrywise characters.

These results concern existence of a nonzero functional and the entire
functional space. They assume no irreducibility, admissibility, finite length,
finite dimension, unitarizability or chosen scalar lines. They do not assert
that any factor or product is generic in the stronger sense that includes
irreducibility and admissibility. They supply the reflection step for a later
Tadic-factor argument, without proving Tadic exhaustion, higher-Speh
nongenericity, strict Hermitian parameters or the final unitary exhaustion.
