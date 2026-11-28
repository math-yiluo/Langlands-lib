# The congruence–Lie homomorphism under local coefficient extension

The theorem
`Langlands.GroupScheme.IntegralModel.congruenceLieUnramifiedCompatibility.{u}`
proves exactly
`Langlands.GroupScheme.IntegralModel.CongruenceLieUnramifiedCompatibilityStatement.{u}`.
Let `F` be a nonarchimedean local field, `G` an affine group scheme over `F`,
`M` a smooth integral model of `G` over `𝒪[F]`, and `n ≤ m ≤ 2n` positive
levels. Let `A = fixedFieldIntegers F` be the integers of the separable inertia
fixed field `inertiaFixedField F`. Then

`(M.baseChangeUnramified.congruenceLieHom _ h hm).comp
    (M.unramifiedCongruenceSubgroupExtend n) =
  ((M.unramifiedCongruenceLieQuotientMap n m).toAddMonoidHom.toMultiplicative).comp
    (M.congruenceLieHom hM h hm)`,

that is, the congruence–Lie homomorphism `G_n → (𝔪ⁿ L)/(𝔪ᵐ L)` commutes with
extension to the maximal unramified extension: on congruence subgroups by the
generic field extension `rationalExtend`, and on Lie-lattice quotients by the
generic tangent extension `GenericLie.baseChange`. No hypothesis beyond those
of the statement is used.

This is the compatibility with unramified base change of the congruence–Lie
map `G_n/G_m → 𝔪ⁿ L/𝔪ᵐ L` of Kaletha and Prasad, *Bruhat–Tits Theory: A New
Approach*, Proposition A.5.19(3) and Remark A.5.20, pp. 642–643
(`kaletha-prasad-2023-bruhat-tits-new-approach`).

## Implemented proof

The module first proves the commuting square for an arbitrary local
coefficient extension and then specialises it. Throughout the general part,
`R` is a local domain with fraction field `K`, `M` is an integral model of an
affine generic group `G` over `R`, and `A` is a local domain with fraction
field `B` and a local homomorphism `R → A`, compatible with a field map
`K → B`. The model `M.baseChange A B` is the pulled-back model, and
`I = congruenceTransitionIdeal R h` and `J = congruenceTransitionIdeal A h` are
the transition ideals `𝔪ⁿ/𝔪ᵐ` in the two congruence rings `R/𝔪ᵐ` and `A/𝔪_Aᵐ`.

It imports `Langlands.GroupScheme.IntegralModel.CongruenceLieFunctorialityProof`
for the factorisation `congruenceLieHom_apply` of `M.congruenceLieHom` as the
reduction `M.congruenceReductionToKernel h` into the square-zero reduction
kernel for `I`, followed by the ideal–Lie tensor comparison
`Lie.SquareZero.kernelTensorAddEquiv M.group I hI` and the equivalence
`M.congruenceLieTensorEquiv hM h`, and for `congruenceIdealReduction_surjective`.
It also imports `Langlands.GroupScheme.IntegralModel.CongruenceLieUnramified`,
which states the target and defines `congruenceRingMap`,
`congruenceSubgroupExtend` and the maps of the statement.

- `congruenceRingAlgHom`: the coefficient map `congruenceRingMap (algebraMap R A) m`
  on congruence rings, as an `R`-algebra map. `congruenceRingAlgHom_mem` shows
  that it carries `I` into `J`, and `algebraMap_mem_maximalIdeal_pow` that
  `R → A` carries `𝔪ⁿ` into `𝔪_Aⁿ`.
- `affineBaseChangeEquiv_baseChange_naturality` restates
  `Lie.affineBaseChangeEquiv_naturality` for the group of `M.baseChange A B`,
  so that coefficient points of the pulled-back model are compared with
  coefficient points of `M` through `Lie.affineBaseChangeEquiv R A M.group`.
- `congruenceKernelExtend`: a point of the reduction kernel of `M.group` for `I`
  is carried along `congruenceRingAlgHom A m` and read, through the inverse
  pullback comparison, as a point of the pulled-back model over `A/𝔪_Aᵐ`. It
  lies in the reduction kernel for `J` because reduction modulo `J` after the
  coefficient map equals the coefficient map on quotients after reduction
  modulo `I`.
- `congruenceKernelExtend_tangentPoint`: the extension of the tangent point
  `Lie.SquareZero.tangentPoint` at an ideal element `i` and a Lie vector `X` is
  the tangent point at the image of `i` and the extended Lie vector
  `M.lieModuleBaseChange X`. After applying the pullback comparison both sides
  are coefficient changes of the dual-number point of `X`, and the two
  coefficient maps `R[ε] → A/𝔪_Aᵐ` agree, which follows from
  `Lie.SquareZero.tangentEvaluation_apply` and the scalar towers.
- `congruenceReductionToKernel_extend`: reduction to the transition kernel
  commutes with `M.congruenceSubgroupExtend A B n` and `congruenceKernelExtend`.
  The extended level-`n` point is represented by the section
  `baseChangeSectionHom (Spec.algebraMap R A) M.group x`
  (`baseChange_integralPointMap`, `rationalExtend_hom_eq_baseChangeSectionHom`),
  and both reductions are compared as morphisms into `M.group` by
  `baseChangeBasePointsEquiv_left` and `baseChangeSectionHom_fst`; the two
  base maps `Spec (A/𝔪_Aᵐ) → Spec R` coincide by `Spec.map_comp`.
- `congruenceLieTensorEquiv_extend`: under the tensor comparisons for `I` and
  `J`, `congruenceKernelExtend` becomes the Lie-lattice quotient map
  `M.lieLatticeQuotientMap (M.baseChange A B) (GenericLie.baseChange R A G) …`.
  The proof is by induction on tensors. For a pure tensor `i ⊗ X`, write `i` as
  the reduction of some `a ∈ 𝔪ⁿ` (`congruenceIdealReduction_surjective`); then
  `kernelTensorAddEquiv_symm_tmul` and `congruenceKernelExtend_tangentPoint`
  reduce the left side to the class of `a • lieMap (lieModuleBaseChange X)`,
  and `lieMap_baseChange` with semilinearity of `GenericLie.baseChange` gives
  the class of the image of `a • lieMap X`. Sums follow from additivity of all
  maps involved.
- `congruenceLieHom_baseChange`: the commuting square for a general local
  coefficient extension. Evaluating at a level-`n` point, `congruenceLieHom_apply`
  and `congruenceReductionToKernel_extend` move the extension onto the
  reduction kernel; writing the reduction as the image of a tensor under the
  inverse ideal–Lie comparison, `congruenceLieTensorEquiv_extend` concludes.
- `congruenceLieUnramifiedCompatibility` introduces the data of the statement
  and applies `congruenceLieHom_baseChange` with `A = fixedFieldIntegers F` and
  `B = inertiaFixedField F`, using the local instances of
  `Langlands.GroupScheme.IntegralModel.CongruenceLieUnramified` for the algebra
  structure, scalar tower and local homomorphism `𝒪[F] → A`, and for the
  affineness of the base-changed generic group. With these instances
  `M.unramifiedCongruenceSubgroupExtend n` and
  `M.unramifiedCongruenceLieQuotientMap n m` are by definition the general
  maps `M.congruenceSubgroupExtend A B n` and the Lie-lattice quotient map
  above.
