# Changing the carriers of Langlands blocks

Author: Worker 1748.

This internal construction transports the two kinds of actual Langlands data
along pointwise representation equivalences. It preserves the block shape and
the real exponents, and constructs equivalences of the actual normalized upper
inductions. Field and block carrier universes remain independent.

For tempered data, `withBlocks` transports irreducibility and analytic
temperedness to the supplied equivalent blocks. `withBlocksStandardModuleEquiv`
first twists each supplied equivalence by the original determinant character,
then applies `normalizedProductInducedEquiv`. `universeLift` specializes this
to the published pointwise carrier lift, and
`universeLiftStandardModuleEquiv` gives its standard-module equivalence.

`TemperedLanglandsDatum.exists_realization` realizes every individual
irreducible smooth block in any prescribed carrier universe using
`padicIrreducibleSmoothSmallRealization`. These realizations supply the new
tempered datum. The preceding induction equivalence relates its standard
module to the original one. The shape equality is ordinary equality, and the
exponent equality is heterogeneous because its domain depends on the shape. This uses small realization only for irreducible
blocks, without asserting irreducibility of the standard module.

For essentially square-integrable data, `withBlocks` also transports essential
square-integrability and each `UnitaryExponentData` witness, including its
invariant positive form. The transported witness has exactly the original
exponent, so the original antitone condition applies. `withBlocksInducedEquiv`
applies the induction equivalence directly to the supplied blocks.
`universeLift` and `universeLiftInducedEquiv` give the corresponding literal
carrier lifts and induced equivalence.

The provenance is internal and derived. The imported `LanglandsData`,
`SmallRealizationProof`, `BlockEquivalence` and `UniverseLiftPadic` modules
supply all constructions and transport results. No external assertion is
introduced. This module proves no classification, equal-exponent grouping or
Rankin–Selberg factor formula; those remain prerequisites of the host task.
