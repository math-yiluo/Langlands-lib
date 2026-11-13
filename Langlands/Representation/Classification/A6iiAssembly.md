# Composition factors of the two standard modules

Author: Worker 4988. Module `Langlands.Representation.Classification.A6iiAssembly`,
namespace `Langlands.Classification.A6ii`. Internal helper for the proof of Tadić's
Corollary A.6(ii) (`IrreducibleLanglandsHeadProductProof`).

- `haveSame_of_equiv`: equivalent representations, one of finite length, have the same
  composition factors (published `FactorMatchingProof.haveSameJordanHolderFactors_of_equiv`).
- `merged_length_eq`, `mergedPerm`: the length equality between `c` and `merged c m`,
  and the permutation of the segments of `c` into merged order.
- `blocks_irreducible_admissible`: the blocks of a datum of segment heads are
  irreducible and admissible. Admissibility comes from the published `cuspidalEmbedding`.
- `jh_concat`: the normalized product over `B` of the standard modules `(d' i).induced`
  has finite length and the composition factors of the concatenated standard module
  (published `concatenateInducedEquiv` and `productInduced_finiteLength`).
- `permute_blockList_eq`: the datum `c` permuted by `mergedPerm` has the block list of
  `merged c m`.
- `induced_hasFiniteLength`: the standard module of a datum of segment heads has finite
  length.
- `permute_haveSame`: permuting the segments of a datum of segment heads keeps the
  composition factors of its standard module (published `permutedProducts`).
- `blockList_haveSame`: data with equal block lists are equal
  (`blockList_injective`), so their standard modules have the same composition factors.
- `jhComparison`: the product of the standard modules of the `d' i` and the standard
  module of `merged (concatenate B d') m` both have finite length and the same
  composition factors. This is the composite of `jh_concat`, `permute_haveSame` and
  `blockList_haveSame`.
- `rankZeroEquiv`: any two normalized products for block shapes of rank `0` are
  equivalent. Both carriers are linearly equivalent to `ℂ`
  (`rankZeroNormalizedProductLinearEquiv`), and `GL_0` is trivial.
