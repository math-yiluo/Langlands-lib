# Original source coefficients of the represented compact integral

This internal adapter compares the actual nested coefficient quotient in the
represented compact integral with the ordinary source-intersection radical
quotient. It retains the action of the whole literal target intersection and
the source inducing half character.

The source projection of the full target section is first identified with the
original intersection Levi projection followed by the supplied original
conjugation map. This uses the existing compatibility of the original two Levi
projections and the common-Levi recovery theorem. The target action is the
ordinary original source Jacquet action through that map, twisted by the
original source inducing half.

The representation equivalence removes the nested intersection using
`splitStagesCoefficientEquiv`, then applies the original class-preserving
stabilizer quotient equivalence. Its previously explicit reverse radical-image
inclusion is supplied by the proved theorem under the retained simultaneous
dynamic realization. The resulting map sends the class of each original
source vector to the class of that same vector. It intertwines the full
target-intersection action and commutes with every original source morphism
and its actual Jacquet quotient map.

Twisting this equivalence by the exact compact-integral Haar character gives
the corresponding natural scalar-twisted coefficient equivalence. This file
does not cancel the outer target normalization or the epsilon corrections,
construct an induced functor isomorphism, supply the dynamic realization, or
prove the closed local orbit-comparison statement.

The provenance is internal: every map is assembled from the existing original
represented point maps, the original projection compatibility, and the already
implemented quotient universal properties. No new literature assertion is used.
