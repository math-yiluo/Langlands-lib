import Langlands.GroupScheme.IntegralModel.CongruenceLieInjectivityProof
import Langlands.GroupScheme.IntegralModel.CongruenceLiftingProof

/-! # Surjectivity of the congruence–Lie homomorphism over a Henselian base -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [HenselianLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)

/-- Over a Henselian local base, every point of the transition kernel is the
reduction of a level-`n` point of a smooth model. -/
theorem congruenceReductionToKernel_surjective (hM : M.IsSmooth) {n m : ℕ+} (h : n ≤ m) :
    Function.Surjective (M.congruenceReductionToKernel h) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ :=
    henselianCongruenceLifting R M.group hM m ((M.congruenceAffinePointsEquiv m).symm y)
  have hx' : M.reductionAt m x = (M.congruenceAffinePointsEquiv m).symm y := hx
  have hn : M.reductionAt n x = 1 := by
    rw [← M.congruenceTransition_reductionAt h, hx',
      ← M.congruenceAffinePointsEquiv_mem_squareZeroKernel_iff h, MulEquiv.apply_symm_apply]
    exact hy
  refine ⟨M.congruenceSubgroupEquiv n ⟨x, hn⟩, Subtype.ext ?_⟩
  rw [M.congruenceReductionToKernel_section, hx', MulEquiv.apply_symm_apply]

variable [IsAffineHom G.X.hom]

/-- Over a Henselian local base the congruence–Lie homomorphism is surjective. -/
theorem congruenceLieHom_surjective (hM : M.IsSmooth) {n m : ℕ+} (h : n ≤ m)
    (hm : (m : ℕ) ≤ 2 * (n : ℕ)) :
    Function.Surjective (M.congruenceLieHom hM h hm) := by
  simp only [congruenceLieHom, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact (MulEquiv.surjective _).comp (M.congruenceReductionToKernel_surjective hM h)

/-- Over a Henselian local base the congruence–Lie homomorphism identifies
`G_n/G_m` with the Lie-lattice quotient. -/
theorem congruenceLieQuotientHom_bijective (hM : M.IsSmooth) {n m : ℕ+} (h : n ≤ m)
    (hm : (m : ℕ) ≤ 2 * (n : ℕ)) :
    Function.Bijective (M.congruenceLieQuotientHom hM h hm) := by
  refine ⟨M.congruenceLieQuotientHom_injective hM h hm, fun y => ?_⟩
  obtain ⟨g, rfl⟩ := M.congruenceLieHom_surjective hM h hm y
  exact ⟨QuotientGroup.mk g, rfl⟩

/-- **KP Proposition A.5.19(3), surjectivity over a Henselian base.** -/
theorem congruenceLieSurjectivity : CongruenceLieSurjectivityStatement.{u} := by
  intro R K _ _ _ _ _ _ G _ M hM n m h hm
  exact ⟨M.congruenceLieHom_surjective hM h hm, M.congruenceLieQuotientHom_bijective hM h hm⟩

end Langlands.GroupScheme.IntegralModel
