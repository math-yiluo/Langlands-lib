# Surjectivity of the congruence–Lie homomorphism over a Henselian base

The theorem
`Langlands.GroupScheme.IntegralModel.congruenceLieSurjectivity.{u}` proves
exactly
`Langlands.GroupScheme.IntegralModel.CongruenceLieSurjectivityStatement.{u}`.
For a smooth integral model `M` over a commutative Henselian local domain
`R : Type u` of an affine generic group `G`, and positive levels
`n ≤ m ≤ 2n`, the homomorphism `M.congruenceLieHom hM h hm` from the level-`n`
congruence subgroup to the Lie-lattice quotient `(𝔪ⁿ L)/(𝔪ᵐ L)` is
surjective, and the induced homomorphism `M.congruenceLieQuotientHom hM h hm`
on `G_n/G_m` is bijective. No hypothesis beyond those of the statement is
used.

This is the surjectivity part of Kaletha and Prasad, *Bruhat–Tits Theory: A
New Approach*, Proposition A.5.19(3) and Remark A.5.20, pp. 642–643, which
rests on the Henselian lifting of Lemma 8.1.3, p. 284
(`kaletha-prasad-2023-bruhat-tits-new-approach`).

## Implemented proof

The module imports `Langlands.GroupScheme.IntegralModel.CongruenceLieInjectivityProof`
for injectivity and `Langlands.GroupScheme.IntegralModel.CongruenceLiftingProof`
for Henselian lifting.

- `congruenceReductionToKernel_surjective` shows that
  `congruenceReductionToKernel h` is onto the square-zero kernel
  `Lie.SquareZero.kernel M.group (congruenceTransitionIdeal R h)`. Given a
  point `y` of this kernel, `henselianCongruenceLifting`, applied to the
  smooth group scheme `M.group` and level `m`, gives an integral section `x`
  whose reduction `reductionAt m x` (which is by definition
  `baseChangeSectionHom (congruenceBaseMap R m) M.group x`) is the point
  corresponding to `y` under `congruenceAffinePointsEquiv m`. By
  `congruenceTransition_reductionAt`, `reductionAt n x` is the image of this
  point under `congruenceTransition h`, which is the identity by
  `congruenceAffinePointsEquiv_mem_squareZeroKernel_iff` because `y` lies in
  the kernel. So `x` lies in `congruenceKernelAt n`, and
  `congruenceReductionToKernel_section` shows that its image under
  `congruenceSubgroupEquiv n` is sent to `y`.
- `congruenceLieHom_surjective`: after unfolding `congruenceLieHom`, the map is
  a `MulEquiv` composed with `congruenceReductionToKernel h`, so it is
  surjective.
- `congruenceLieQuotientHom_bijective`: injectivity is
  `congruenceLieQuotientHom_injective` from the injectivity module; every
  value `congruenceLieHom hM h hm g` is the value of the quotient map at the
  class of `g` (`congruenceLieQuotientHom_mk`), so surjectivity follows from
  the previous item.
- `congruenceLieSurjectivity` introduces the data of the statement and
  combines the last two items.
