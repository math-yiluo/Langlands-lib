# Finite coefficient models of affine fppf group quotients

Worker 875. Internal derivation from actual flat affine homomorphism models,
published relative flatness and surjectivity descent, and the actual
group-scheme kernel.

`FlatAffineQuotientModel R A f` records a simultaneous affine flat
finite-presentation group model with a flat surjective model homomorphism.
`FlatAffineHomModel.exists_flatSurjective` enlarges any existing model of a
flat surjective map until both properties hold over the coefficient ring.
The recovery isomorphisms transport both properties over `A`; the relative
descent theorems place each property at a finite stage, and a common larger
stage has both.

`exists_flatAffineQuotientModel` retains a prescribed finite coefficient
subset. `flatAffineQuotientModel` chooses a model. The model map is locally
of finite presentation because its source is of finite presentation over
the coefficient ring and its target is locally of finite type over it.

`FlatAffineQuotientModel.isFppfQuotient_kernel` gives the exact fppf quotient
sequence with the actual model kernel, whose full all-test image is the
kernel image by definition. The kernel is affine, flat and locally of finite
presentation over the same coefficient ring: its structure morphism is
the base change of the quotient map along the unit section, and its inclusion
is closed because the target group is separated.

All rings lie in the same arbitrary universe. There is no smoothness,
commutativity or quasi-finiteness premise. This construction does not assert
that the model kernel or quotient is of multiplicative type, and does not
choose an identification with an additional supplied kernel representative.
