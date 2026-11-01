# Rational automorphism and CM actions on adelic growth spaces

Author: Worker 2.

For an actual number field in any universe and every natural matrix rank,
including zero, this internal construction acts on the three existing growth
spaces from `Automorphic.Growth`: polynomial-growth continuous rational
functions, their slice-wise smooth subspace, and their real-smooth subspace
with a common open finite stabilizer. Growth retains the existing concrete
matrix/inverse height and the existing finite-slice-dependent bounds. The
complex coefficients and values are fixed.

`polynomialGrowthGaloisAut`, `smoothPolynomialGrowthGaloisAut`, and
`finiteSmoothPolynomialGrowthGaloisAut` are monoid homomorphisms from actual
rational field automorphisms to continuous complex-linear automorphisms.
They use the corresponding arithmetic growth equivalence along the inverse
field automorphism. The proved identity and contravariant composition laws
supply their homomorphism laws. The corresponding `GaloisAction` definitions
are installable additive left actions; no global action instance is installed.

For each space, the underlying ambient function is the existing `galoisAut`.
The evaluation formula uses the actual inverse arithmetic adelic matrix map.
Full right translation is intertwined with inverse arithmetic transport of
the group argument. Existence of compact open finite level is preserved and
reflected, and membership in the specified central-character space is
transported by the existing Hecke-character Galois action.

For an actual CM field, `polynomialGrowthComplexConj`,
`smoothPolynomialGrowthComplexConj`, and
`finiteSmoothPolynomialGrowthComplexConj` are direct argument pullbacks by
the existing actual CM adelic matrix involution. They agree with the ambient
`complexConj`, are involutive, and agree with the rational inverse-pullback
action after restricting the CM automorphism to rational scalars. Their full
right-translation covariance and evaluation formulas use the actual
`CMConjugation.adelicConj`.

Each CM map preserves and reflects compact open finite level and finiteness
of the orbit span under the actual `standardInfiniteCompact`. The latter
uses its already proved CM invariance. The specified character changes by
the existing `HeckeCharacter.complexConj`, with exact value
`chi (ideleClassComplexConj x)`. No identification of the standard compact
under an arbitrary field isomorphism is needed or asserted.

The actual common-stabilizer-to-slice-smooth growth inclusion commutes with
both actions. Forgetting growth from either smooth growth space gives the
previously constructed smooth rational or CM action exactly.

Provenance is internal restriction and specialization of
`GrowthArithmeticTransport`, `SmoothArithmeticActions`, and the ambient
arithmetic transport laws. All preservation claims use their proved
intrinsic laws on actual subspaces. Continuity refers to the inherited
compact-open topology. This file supplies no derivative-topology assertion,
enveloping-center finiteness or cuspidality preservation, automorphic
occurrence, spectral existence, or classification theorem.
