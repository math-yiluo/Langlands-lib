# Restricting opposite dual Jacquet vectors to a consecutive coarsening

Module `Langlands.Representation.Exponents.WeakCriticalTopLayerCoarsening`.
Internal helper module (no source statement); author Worker 728.

## Setting

`B` and `C` are block shapes of `n`, and `q : Fin B.length → Fin C.length` is a
monotone map whose fibres have the block sizes of `C`
(`C.size j = ∑ i with q i = j, B.size i`). So `C` is a consecutive coarsening of
`B`. This is the hypothesis pair used by the Library lemmas
`isDualJacquetExponent_coarsen`, `leviModulus_blockScalarLevi_coarsen` and
`BlockShape.oppositeUnipotentSubgroup_le_of_coarsen` (module
`Classification/MaximalConeExponents`).

A vector of `T.splitCentreDualJacquet B A`, the full algebraic dual of the
normalized opposite Jacquet module of `A` along `B`, is the same as a source
functional on `A` invariant under the opposite radical of `B`
(`T.splitCentreDualJacquetSourceEquiv`). The opposite radical of `C` is
contained in that of `B`, so the same source functional is invariant under the
opposite radical of `C`.

## Declarations

- `subgroupInvariantDual_le_of_coarsen`: the inclusion of the spaces of
  invariant source functionals.
- `dualJacquetCoarsen hq hsize A`: the linear map
  `T.splitCentreDualJacquet B A →ₗ[ℂ] T.splitCentreDualJacquet C A` that keeps
  the source functional. It is the composite of the source equivalence for `B`,
  the inclusion above, and the inverse source equivalence for `C`.
- `splitCentreDualJacquetSource_action`: the Library formula
  `splitCentreDualJacquet_apply_mk`, restated through the source equivalence.
  The block scalar `a` multiplies by the half modulus and acts on the source.
- `splitCentreDualJacquet_ext`: dual vectors with equal source functionals are
  equal.
- `dualJacquetCoarsen_source`: the source functional is unchanged.
- `dualJacquetCoarsen_injective`.
- `dualJacquetCoarsen_comm`: for a coarse block scalar `c`, the restriction
  intertwines the fine action of `c ∘ q` with the coarse action of `c`. The
  proof evaluates both sides on source vectors. It uses that the embedded
  block scalars agree (`leviEmbedding_blockScalarLevi_coarsen`) and that the
  half moduli agree (`leviModulus_blockScalarLevi_coarsen`).
- `dualJacquetCoarsen_defect_pow`: the same for every power of a character
  defect `(ρ c - z • 1) ^ k`, by induction on `k`.
- `dualJacquetCoarsen_mem_generalized`: a generalized `ψ`-vector along `B`
  restricts to a generalized vector along `C` for the restricted character
  `ψ.comp (MaximalConeAssembly.precomp q)`, with the same power.

## Use

`WeakCriticalTopLayerL2Reduction` applies these maps to the coarsening of a
flattened shape `B.flatten D` to a shape that splits one block of `B`. They
carry a generalized vector with a nonvanishing defect power from the fine shape
to the coarse shape. This bounds the nilpotence index along the coarse shape
from below.
