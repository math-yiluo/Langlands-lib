# Finite coefficient models of extensions with diagonalizable endpoints

This module combines actual affine fppf quotient models, finite
coefficient isomorphism descent and published kernel comparison isomorphisms.

`FlatAffineHomModel.kernelRecoveryIso` identifies the model kernel after base
change with the actual kernel of the original homomorphism. Its inclusion
formula follows from the kernel base-change comparison and the isomorphism
of arrows given by the recovery square.
`FlatAffineQuotientModel.enlarge` preserves flatness and surjectivity of the
model quotient under a further finite coefficient enlargement.

`SplitFlatAffineQuotientModel R A f` records an affine fppf quotient model
whose actual kernel and quotient are diagonalizable. Given diagonalizability
of the original kernel and quotient, `exists_splitFlatAffineQuotientModel`
constructs such a model while retaining any prescribed finite subset of `A`.
The proof first chooses a quotient model. It descends a diagonalizable
presentation of its kernel to finite coefficients, using the kernel recovery
isomorphism. A second enlargement descends a diagonalizable presentation of
the quotient. The previously obtained kernel presentation is preserved by
base change and the kernel base-change isomorphism.

`splitFlatAffineQuotientModel` chooses a model. Its inherited quotient data
give an exact fppf sequence with the actual model kernel, which is affine,
flat and locally of finite presentation. The source and quotient are
affine, flat and locally of finite presentation, and the recovery square
recovers the original quotient map. The model's coefficient ring is
noetherian whenever the initial ground ring is, by
`SplitFlatAffineQuotientModel.noetherian`.

All schemes and rings lie in the same arbitrary universe. Both endpoint
presentations use finitely generated full character groups, including
torsion. The construction imposes no smoothness or commutativity premise
on the middle group. It does not prove the middle group to be of
multiplicative type.

`kernelRepresentativeRecoveryIso` further identifies the model kernel over
`A` with any supplied monomorphic representative of the original full kernel.
Its inclusion formula recovers the original kernel homomorphism.
`exists_splitFlatAffineQuotientModel_of_quotient` accepts this formulation of
an exact sequence directly, with diagonalizable supplied kernel and quotient,
and produces the same finite coefficient model.
