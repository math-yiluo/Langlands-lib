import Langlands.GroupScheme.IntegralModel.CongruenceLieFunctorialityProof

/-! # Adjoint equivariance of the congruence–Lie homomorphism

For a smooth integral model `M` of `G` over a local domain `R` and an integral
point `g`, the congruence–Lie homomorphism of `M` (KP Proposition A.5.19(3))
carries conjugation by `g` on the level-`n` congruence subgroup to the adjoint
action of `g` on the Lie-lattice quotient `(𝔪ⁿ L)/(𝔪ᵐ L)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 120000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))} {M : IntegralModel R K G}

/-- The reduction of an integral section to level `m`, read as a coefficient point
of the model, is the coefficient change of its `R`-coefficient point. -/
theorem congruenceAffinePointsEquiv_reductionAt (m : ℕ+) (y : M.integralSections) :
    M.congruenceAffinePointsEquiv m (M.reductionAt m y) =
      Lie.affineMap M.group (Algebra.ofId (CommRingCat.of R) (congruenceRing R m))
        (AffineWeil.sectionsCoeffEquiv R M.group y) := by
  apply Over.OverMorphism.ext
  change (baseChangeBasePointsEquiv (congruenceBaseMap R m) M.group (M.reductionAt m y)).left = _
  rw [baseChangeBasePointsEquiv_left]
  change (baseChangeSectionHom (congruenceBaseMap R m) M.group y).left ≫
      pullback.fst M.group.X.hom (congruenceBaseMap R m) = _
  rw [baseChangeSectionHom_fst, Lie.affineMap_apply, Over.comp_left,
    AffineWeil.sectionsCoeffEquiv_left]
  rfl

/-- Conjugation by an integral point commutes with the reduction of level-`n`
points to the transition kernel, where on the kernel it is conjugation by the
reduced coefficient point. -/
theorem congruenceReductionToKernel_conj (g : M.integralPoints) (y : M.integralSections)
    (hy : M.integralPointMap y = g.val) {n m : ℕ+} (h : n ≤ m)
    (k : M.congruenceSubgroupAt n) :
    M.congruenceReductionToKernel h (M.congruenceSubgroupConj g n k) =
      Lie.SquareZero.kernelConjugation M.group (congruenceTransitionIdeal R h)
        (Lie.affineMap M.group (Algebra.ofId (CommRingCat.of R) (congruenceRing R m))
          (AffineWeil.sectionsCoeffEquiv R M.group y))
        (M.congruenceReductionToKernel h k) := by
  obtain ⟨x, rfl⟩ := (M.congruenceSubgroupEquiv n).surjective k
  have hx : ((M.congruenceSubgroupEquiv n).symm
      (M.congruenceSubgroupConj g n (M.congruenceSubgroupEquiv n x))).val =
      y * x.val * y⁻¹ := by
    apply M.integralPointMap_injective
    rw [map_mul, map_mul, map_inv, hy]
    rw [← congruenceSubgroupEquiv_val, MulEquiv.apply_symm_apply]
    rfl
  apply Subtype.ext
  rw [Lie.SquareZero.kernelConjugation_val, M.congruenceReductionToKernel_section,
    ← congruenceAffinePointsEquiv_reductionAt]
  change M.congruenceAffinePointsEquiv m (M.reductionAt m ((M.congruenceSubgroupEquiv n).symm
    (M.congruenceSubgroupConj g n (M.congruenceSubgroupEquiv n x))).val) = _
  rw [hx, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]

variable [IsAffineHom G.X.hom]

/-- **KP Proposition A.5.19(3), adjoint equivariance.** -/
theorem congruenceLieHom_conj (hM : M.IsSmooth) (g : M.integralPoints) {n m : ℕ+}
    (h : n ≤ m) (hm : (m : ℕ) ≤ 2 * (n : ℕ)) :
    (M.congruenceLieHom hM h hm).comp (M.congruenceSubgroupConj g n) =
      ((M.congruenceLieQuotientAdjoint g n m).toAddMonoidHom.toMultiplicative).comp
        (M.congruenceLieHom hM h hm) := by
  have : Smooth M.group.X.hom := hM
  have hI := congruenceTransitionAlgHom_ker_sq R h (by omega)
  obtain ⟨y, hy⟩ := g.property
  refine MonoidHom.ext fun k => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, congruenceLieHom_apply,
    congruenceLieHom_apply, congruenceReductionToKernel_conj g y hy h]
  set r := M.congruenceReductionToKernel h k
  obtain ⟨z, hz⟩ := (Lie.SquareZero.kernelTensorAddEquiv M.group
    (congruenceTransitionIdeal R h) hI).symm.surjective (Additive.ofMul r)
  have hr : r = ((Lie.SquareZero.kernelTensorAddEquiv M.group
      (congruenceTransitionIdeal R h) hI).symm z).toMul := by rw [hz]; rfl
  rw [hr, Lie.SquareZero.kernelTensorAddEquiv_conjugation, ofMul_toMul,
    AddEquiv.apply_symm_apply]
  exact congrArg Multiplicative.ofAdd (congruenceLieTensorEquiv_map hM hM _ _
    (fun X => by rw [← hy]; exact M.lieMap_adjoint y X)
    (fun _ hX => M.adjoint_mem_lieLattice g.property hX) (by simp) h z)

/-- **KP Proposition A.5.19(3), adjoint equivariance.** -/
theorem congruenceLieAdjointEquivariance :
    CongruenceLieAdjointEquivarianceStatement.{u} := by
  intro R K _ _ _ _ _ _ G _ M hM g n m h hm
  exact congruenceLieHom_conj hM g h hm

end Langlands.GroupScheme.IntegralModel
