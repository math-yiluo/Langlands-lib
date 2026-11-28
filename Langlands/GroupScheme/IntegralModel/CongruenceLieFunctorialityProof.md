# Functoriality of the congruence–Lie homomorphism

The theorem
`Langlands.GroupScheme.IntegralModel.congruenceLieFunctoriality.{u}` proves
exactly
`Langlands.GroupScheme.IntegralModel.CongruenceLieFunctorialityStatement.{u}`.
Let `R : Type u` be a commutative local domain with fraction field `K`, let
`M` and `N` be smooth integral models of affine generic groups `G` and `H`,
let `f : G ⟶ H` be a homomorphism and `φ : M.Hom N f` a model homomorphism
extending it, and let `n ≤ m ≤ 2n` be positive levels. Then

`(N.congruenceLieHom hN h hm).comp (φ.congruenceSubgroupMap n) =
  ((φ.congruenceLieQuotientMap n m).toAddMonoidHom.toMultiplicative).comp
    (M.congruenceLieHom hM h hm)`,

that is, the congruence–Lie homomorphism `G_n → (𝔪ⁿ L)/(𝔪ᵐ L)` commutes with
`f` on the congruence subgroups and with the differential of `f` on the
Lie-lattice quotients. No hypothesis beyond those of the statement is used.

This is the functoriality part of Kaletha and Prasad, *Bruhat–Tits Theory: A
New Approach*, Proposition A.5.19(3) and Remark A.5.20, pp. 642–643
(`kaletha-prasad-2023-bruhat-tits-new-approach`).

## Implemented proof

The homomorphism `M.congruenceLieHom hM h hm` is by definition the composite of
three maps (`congruenceLieHom_apply`, which holds by `rfl`):

1. `M.congruenceReductionToKernel h`, sending a level-`n` point to its
   reduction modulo `𝔪ᵐ`, a point of the square-zero reduction kernel
   `Lie.SquareZero.kernel M.group I` for the transition ideal
   `I = congruenceTransitionIdeal R h` (that is, `𝔪ⁿ/𝔪ᵐ` in `R/𝔪ᵐ`);
2. the ideal–Lie tensor comparison
   `Lie.SquareZero.kernelTensorAddEquiv M.group I hI`, an additive
   equivalence onto `I ⊗[R] Additive (lieKernel M.group R)`;
3. the equivalence `M.congruenceLieTensorEquiv hM h` of this tensor product
   with the Lie-lattice quotient.

The proof shows that each of the three maps commutes with the map induced by
`φ`.

- **Square-zero kernels.** `Lie.SquareZero.kernelTargetMap I f` is
  postcomposition with a group-scheme homomorphism `f : G ⟶ H` over `Spec R`,
  as a homomorphism of reduction kernels modulo `I`. Postcomposition commutes
  with tangent evaluation (`kernelTargetMap_tangentPoint`), and, using the
  pure-tensor formula `kernelTensorAddEquiv_symm_tmul` together with
  `lieKernelMap_target`, induction on tensors gives
  `kernelTensorAddEquiv_target`: under the ideal–Lie comparison,
  `kernelTargetMap I f` becomes `TensorProduct.map LinearMap.id
  (Lie.targetMapLinear f R)`. The same argument with `tangentPoint_adjoint`
  and `adjoint_naturality` gives `kernelTensorAddEquiv_conjugation`: conjugation
  by the image in `A` of a point `c` over `R` becomes `TensorProduct.map
  LinearMap.id (adjoint G R c)`. The latter is not used for functoriality; it
  is the corresponding step for conjugation by integral points.
- **Reduction.** `Hom.congruenceReductionToKernel_naturality` shows that
  reducing `φ.congruenceSubgroupMap n g` is `kernelTargetMap I φ.hom` applied
  to the reduction of `g`. It writes `g` as the generic point of an integral
  point (`congruenceSubgroupEquiv`), uses `Hom.integralPointMap_naturality`
  and `congruenceReductionToKernel_section`, and then
  `Hom.reductionAt_naturality` and `baseChangeBasePointsEquiv_comp`.
- **Tensor comparison.** `congruenceLieTensorEquiv_map` is proved for any
  linear map `d : M.LieModule →ₗ[R] N.LieModule` and linear map
  `D : GenericLie R G →ₗ[R] GenericLie R H` with
  `N.lieMap (d X) = D (M.lieMap X)` that carries the lattice of `M` into the
  lattice of `N`: `N.congruenceLieTensorEquiv` applied to
  `TensorProduct.map LinearMap.id d z` equals `M.lieLatticeQuotientMap N D`
  applied to `M.congruenceLieTensorEquiv z`. By induction on `z` it suffices to
  treat `i ⊗ X`; writing `i` as the reduction of some `a ∈ 𝔪ⁿ`
  (`congruenceIdealReduction_surjective`), both sides are computed by
  `congruenceLieTensorEquiv_tmul` and agree because `D (a • M.lieMap X) =
  a • N.lieMap (d X)`.
- **Assembly.** `Hom.congruenceLieHom_naturality` evaluates both sides at `g`,
  rewrites the reduction by `Hom.congruenceReductionToKernel_naturality`,
  writes the reduction of `g` as the image of a tensor `z` under the inverse
  ideal–Lie comparison, applies `kernelTensorAddEquiv_target`, and concludes by
  `congruenceLieTensorEquiv_map` with `d = Lie.targetMapLinear φ.hom R`, the
  differential of the integral homomorphism, and `D = GenericLie.map R f`; the required identity
  `N.lieMap (d X) = D (M.lieMap X)` is `Hom.lieMap_naturality`, and the lattice
  condition comes from `Hom.map_lieLattice_le`.
- `congruenceLieFunctoriality` introduces the data of the statement and
  applies `Hom.congruenceLieHom_naturality`.
