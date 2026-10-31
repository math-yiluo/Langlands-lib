# Filtered symmetrization after removing prescribed Lie directions

Author: Worker 94. Internal algebraic consequence of the actual symmetric
algebra, enveloping filtration and strict symmetrization product comparison.
This module proves the direction-removal comparison needed for Cartan
restriction. No PBW injectivity or finite central-generation hypothesis is
assumed.

The declarations use a field `R : Type` and an arbitrary Lie algebra
`L : Type v`. Symmetrization comparisons additionally require characteristic
zero; the symmetric telescoping and module-action lemmas do not. A linear endomorphism `f` removes directions in a submodule `M` when
`X - f X` belongs to `M` for every Lie vector `X`; idempotence is unnecessary.
`rightGeneratorRemainder M d` is the sum of the enveloping degree piece `F_d`
and `F_d` times the image of `M` under the actual Lie generator map. It
therefore allows one prescribed generator on the right of a bounded
coefficient.

The symmetric difference between a tensor of degree at most `d` and its
image under the induced symmetric map belongs to the product of the
symmetric degree piece `d - 1` with the symmetric image of `M`. The proof
telescopes monomials, retaining one removed vector in each term. The
product-comparison theorem moves that vector to the right after
symmetrization, at the cost of a degree `d - 1` enveloping error.

The multiplication version compares the product of symmetrizations of
bounded tensors `P` and `Q` with symmetrization of the restricted `P` times
`Q`, provided the induced symmetric map fixes `Q`. Its error belongs to
`rightGeneratorRemainder M (p + q - 1)`. Finally, on any genuine enveloping
module with a generating subspace `W` preserved by the generators from
`M`, such a remainder acts into `F_(p+q-1) W`: the rightmost prescribed
generator is absorbed by `W`.

At degree zero the difference is zero; natural subtraction in the stated
bound does not assert a negative degree piece. These comparisons are
algebraic prerequisites. They do not prove finite central generation or
automorphic derivative growth.
