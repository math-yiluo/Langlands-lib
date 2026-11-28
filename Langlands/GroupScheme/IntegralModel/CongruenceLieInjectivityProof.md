# The kernel of the congruence–Lie homomorphism

The theorem
`Langlands.GroupScheme.IntegralModel.congruenceLieInjectivity.{u}` proves
exactly
`Langlands.GroupScheme.IntegralModel.CongruenceLieInjectivityStatement.{u}`.
For a smooth integral model `M` over a commutative local domain `R : Type u`
of an affine generic group `G`, and positive levels `n ≤ m ≤ 2n`, the kernel
of `M.congruenceLieHom hM h hm` is the level-`m` congruence subgroup, viewed
as `(M.congruenceSubgroupAt m).subgroupOf (M.congruenceSubgroupAt n)`, and the
induced homomorphism `M.congruenceLieQuotientHom hM h hm` on `G_n/G_m` is
injective. No hypothesis beyond those of the statement is used.

This is the kernel and injectivity part of Kaletha and Prasad, *Bruhat–Tits
Theory: A New Approach*, Proposition A.5.19(3) and Remark A.5.20,
pp. 642–643 (`kaletha-prasad-2023-bruhat-tits-new-approach`).

## Implemented proof

The homomorphism `congruenceLieHom` of the module
`Langlands.GroupScheme.IntegralModel.CongruenceLie` is the composite of
`congruenceReductionToKernel h`, with values in the square-zero kernel
`Lie.SquareZero.kernel M.group (congruenceTransitionIdeal R h)`, and a
multiplicative equivalence built from `Lie.SquareZero.kernelTensorAddEquiv`
and `congruenceLieTensorEquiv`. Only the first map can contribute to the
kernel.

- `congruenceReductionToKernel_eq_one_iff` shows that a level-`n` point `g`
  is sent to the identity by `congruenceReductionToKernel h` exactly when it
  lies in `(M.congruenceSubgroupAt m).subgroupOf (M.congruenceSubgroupAt n)`.
  Write `g` as the image under `congruenceSubgroupEquiv n` of an integral
  section `x` of level `n`. By `congruenceReductionToKernel_section`, the
  value at `g` is `congruenceAffinePointsEquiv m (reductionAt m x)`. Since
  `congruenceAffinePointsEquiv m` is a multiplicative equivalence, this is the
  identity exactly when `reductionAt m x = 1`, that is, when `x` has level `m`
  and `g` lies in `congruenceSubgroupAt m`. For the converse inclusion, a
  level-`m` section with the same generic image as `x` equals `x` by
  `integralPointMap_injective`.
- `congruenceLieHom_ker` rewrites membership in the kernel of
  `congruenceLieHom` as the vanishing of `congruenceReductionToKernel h g`:
  unfolding `congruenceLieHom`, the remaining map is a `MulEquiv`, so
  `MulEquiv.map_eq_one_iff` applies. The previous lemma concludes.
- `congruenceLieQuotientHom_injective` uses `injective_iff_map_eq_one`. On a
  class `QuotientGroup.mk g`, the value is `congruenceLieHom hM h hm g`
  (`congruenceLieQuotientHom_mk`); if it is the identity, then `g` lies in the
  kernel, which is the deeper subgroup by `congruenceLieHom_ker`, so the class
  is trivial by `QuotientGroup.eq_one_iff`.
- `congruenceLieInjectivity` introduces the data of the statement and
  combines `congruenceLieHom_ker` and `congruenceLieQuotientHom_injective`.

The proof does not use the Henselian property, smoothness beyond its role in
the definition of `congruenceLieHom`, or the bound `m ≤ 2n` beyond the same.
