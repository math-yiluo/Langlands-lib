# Block scalars on Weyl transports of block tensors

Author: Worker 964.

Module `Langlands.Representation.Classification.SegmentFullJacquetCentral`,
namespace `Langlands.SegmentFullJacquet`. This is an internal helper for the proof
of `Langlands.Classification.SegmentFullJacquetFormula` (Zelevinsky 1980, 3.1 and
9.1(*)). It introduces no literature statement. It computes how a central element
of the uniform Levi `GL_r × ⋯ × GL_r` acts on the Weyl transports of the segment
tensor, and it shows that one such element separates all of these transports.
This central-character argument is the implemented route. It replaces the
multiplicity bookkeeping of Zelevinsky 1980, §2.

## Block scalars and transports

For a field `F`, block shapes `B, C` of `n` and a Levi-conjugating permutation `w`:

- `leviConjugation_symm_blockScalarLevi`. Let `g` be a block map with
  `blockIndex C (w a) = g (blockIndex B a)`. Inverse Levi conjugation sends the
  block scalar `C.blockScalarLevi F t` to `B.blockScalarLevi F (t ∘ g)`. Proof:
  apply `leviEmbedding` (injective), then compare the entries of the conjugated
  diagonal matrix (`permutation_conjugate_entry`, `coe_blockScalar`).
- `blockTensor_blockScalarLevi`. If each factor `σ i` has scalar character `ω i`
  on the scalar matrices, a block scalar with entries `s` acts on the block tensor
  by `∏ i, ω i (s i)`. Proof: induction on the tensor
  (`PiTensorProduct.induction_on`).
- `transport_blockTensor_blockScalarLevi`. On the transport of the block tensor
  by `w`, the block scalar with entries `t` acts by
  `∏ i, ω i (t (blockMap B C w i))`. This combines the two previous lemmas with
  `TotalConjugatingCount.blockIndex_apply`.

## Combinatorics

- `digits_sum_injective`: base-`b` expansions with digits below `b` are unique
  (induction on the number of digits, using `% b` and `/ b`).
- `perm_eq_of_weightedSum_eq`: a permutation `g` of `Fin m` is determined by
  `∑ i, i * m ^ g i`. Reindex to `∑ j, g⁻¹ j * m ^ j` and apply the previous lemma.
- `exists_descent_of_ne_one`: a permutation other than the identity has a
  descent `g (k + 1) < g k`. Otherwise it is strictly monotone
  (`Fin.strictMono_iff_lt_succ`), hence the identity
  (`StrictMono.range_inj_of_wellFoundedLT`).
- `exists_ascent_of_ne_rev`: a permutation other than the reversal has an ascent;
  apply the previous lemma to `Fin.revPerm * g`.

## The separating scalars

Let `T` be the topological data of a `p`-adic field, `ϖ` its specified uniformizer
(`LocalFactor.PadicAbelian.uniformizerUnit T`) and `q⁻¹ = |ϖ|`.

- `separatingEntries T m j = ϖ ^ (m ^ j)`. `uniformizerAbs T` is `|ϖ|`, with
  `uniformizerAbs_pos` and `uniformizerAbs_lt_one`. The latter uses
  `normalizedAbs_uniformizer` and `residueCardinality_gt_one`.
- `segmentScalar T ω r m g = ∏ i, (ω ⊗ |det|^i)(ϖ ^ (m ^ g i))`. This is the
  scalar by which the separating element acts when block `i` carries
  `ν^i A` and the transport has block map `g`. Here `ω` is a scalar character of
  `A`.
- `segmentScalar_eq`: for a permutation `g`,
  `segmentScalar T ω r m g = (∏ j, ω (ϖ ^ (m ^ j))) * |ϖ| ^ (r * ∑ i, i * m ^ g i)`.
- `segmentScalar_injective`: for `0 < r`, distinct block permutations give
  distinct scalars. Cancel the nonzero first factor, use the strict
  antitonicity of `n ↦ |ϖ| ^ n`, then apply `perm_eq_of_weightedSum_eq`.
