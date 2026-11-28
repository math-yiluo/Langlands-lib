# Adjoint equivariance of the congruence–Lie homomorphism

The theorem
`Langlands.GroupScheme.IntegralModel.congruenceLieAdjointEquivariance.{u}`
proves exactly
`Langlands.GroupScheme.IntegralModel.CongruenceLieAdjointEquivarianceStatement.{u}`.
Let `R : Type u` be a commutative local domain with fraction field `K`, let
`M` be a smooth integral model of an affine generic group `G`, let
`g : M.integralPoints` be an integral point and let `n ≤ m ≤ 2n` be positive
levels. Then

`(M.congruenceLieHom hM h hm).comp (M.congruenceSubgroupConj g n) =
  ((M.congruenceLieQuotientAdjoint g n m).toAddMonoidHom.toMultiplicative).comp
    (M.congruenceLieHom hM h hm)`,

that is, the congruence–Lie homomorphism `G_n → (𝔪ⁿ L)/(𝔪ᵐ L)` carries
conjugation by `g` on the level-`n` congruence subgroup to the adjoint action
`GenericLie.adjoint R g` of `g`, restricted to the Lie-lattice quotient. No
hypothesis beyond those of the statement is used.

This is the equivariance, under conjugation by the integral points `𝒢(R)`,
of the congruence–Lie map `G_n/G_m → 𝔪ⁿ L/𝔪ᵐ L` of Kaletha and Prasad,
*Bruhat–Tits Theory: A New Approach*, Proposition A.5.19(3) and Remark A.5.20,
pp. 642–643 (`kaletha-prasad-2023-bruhat-tits-new-approach`).

## Implemented proof

The module imports
`Langlands.GroupScheme.IntegralModel.CongruenceLieFunctorialityProof`, which
writes `M.congruenceLieHom hM h hm` as the composite of the reduction
`M.congruenceReductionToKernel h` into the square-zero reduction kernel for the
transition ideal `I = congruenceTransitionIdeal R h`, the ideal–Lie tensor
comparison `Lie.SquareZero.kernelTensorAddEquiv M.group I hI`, and the
equivalence `M.congruenceLieTensorEquiv hM h` (`congruenceLieHom_apply`), and
which proves the two compatibilities used below
(`Lie.SquareZero.kernelTensorAddEquiv_conjugation` and
`congruenceLieTensorEquiv_map`).

Write `g` as the generic point `M.integralPointMap y` of an integral section
`y`, and let `c = AffineWeil.sectionsCoeffEquiv R M.group y` be its
`R`-coefficient point.

- `congruenceAffinePointsEquiv_reductionAt`: the reduction
  `M.reductionAt m y`, read as a coefficient point through
  `congruenceAffinePointsEquiv m`, is the coefficient change of `c` along
  `R → R/𝔪ᵐ`. Both sides are compared on underlying morphisms, using
  `baseChangeBasePointsEquiv_left`, `baseChangeSectionHom_fst` and
  `AffineWeil.sectionsCoeffEquiv_left`.
- `congruenceReductionToKernel_conj`: reducing the conjugate of a level-`n`
  point by `g` gives the conjugate, by the reduced coefficient point of the
  previous item, of its reduction; this is
  `Lie.SquareZero.kernelConjugation`. The integral section underlying the
  conjugate is `y * x * y⁻¹` by `integralPointMap_injective`, and reduction
  and the point comparison are multiplicative.
- `congruenceLieHom_conj` evaluates both sides at a level-`n` point,
  rewrites the reduction by `congruenceReductionToKernel_conj`, writes the
  reduction as the image of a tensor `z` under the inverse ideal–Lie
  comparison, and applies `kernelTensorAddEquiv_conjugation`, which turns
  conjugation into `TensorProduct.map LinearMap.id (adjoint M.group R c)`.
  It concludes by `congruenceLieTensorEquiv_map` with
  `d = adjoint M.group R c` and `D = GenericLie.adjoint R g`; the required
  identity `M.lieMap (d X) = D (M.lieMap X)` is `lieMap_adjoint`, and the
  lattice condition is `adjoint_mem_lieLattice`.
- `congruenceLieAdjointEquivariance` introduces the data of the statement and
  applies `congruenceLieHom_conj`.
