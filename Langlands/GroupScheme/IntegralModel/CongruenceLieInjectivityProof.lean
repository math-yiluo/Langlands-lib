import Langlands.GroupScheme.IntegralModel.CongruenceLieStatements

/-! # The kernel of the congruence–Lie homomorphism -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)

/-- A level-`n` point reduces to the identity modulo `𝔪ᵐ` exactly when it has level `m`. -/
theorem congruenceReductionToKernel_eq_one_iff {n m : ℕ+} (h : n ≤ m)
    (g : M.congruenceSubgroupAt n) :
    M.congruenceReductionToKernel h g = 1 ↔
      g ∈ (M.congruenceSubgroupAt m).subgroupOf (M.congruenceSubgroupAt n) := by
  obtain ⟨x, rfl⟩ := (M.congruenceSubgroupEquiv n).surjective g
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    have h1 := congrArg Subtype.val hg
    rw [M.congruenceReductionToKernel_section] at h1
    have h2 : M.reductionAt m x.val = 1 :=
      (M.congruenceAffinePointsEquiv m).injective (h1.trans (map_one _).symm)
    exact ⟨x.val, h2, rfl⟩
  · rintro ⟨y, hy, hyg⟩
    have hxy : y = x.val := M.integralPointMap_injective hyg
    apply Subtype.ext
    rw [M.congruenceReductionToKernel_section, ← hxy, hy, map_one]
    rfl

variable [IsAffineHom G.X.hom]

/-- The kernel of the congruence–Lie homomorphism is the deeper congruence subgroup. -/
theorem congruenceLieHom_ker (hM : M.IsSmooth) {n m : ℕ+} (h : n ≤ m)
    (hm : (m : ℕ) ≤ 2 * (n : ℕ)) :
    (M.congruenceLieHom hM h hm).ker =
      (M.congruenceSubgroupAt m).subgroupOf (M.congruenceSubgroupAt n) := by
  ext g
  rw [MonoidHom.mem_ker, ← M.congruenceReductionToKernel_eq_one_iff h]
  simp only [congruenceLieHom, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

/-- The congruence–Lie homomorphism is injective on `G_n/G_m`. -/
theorem congruenceLieQuotientHom_injective (hM : M.IsSmooth) {n m : ℕ+} (h : n ≤ m)
    (hm : (m : ℕ) ≤ 2 * (n : ℕ)) :
    Function.Injective (M.congruenceLieQuotientHom hM h hm) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [congruenceLieQuotientHom_mk, ← MonoidHom.mem_ker, M.congruenceLieHom_ker hM h hm] at hq
    exact (QuotientGroup.eq_one_iff g).mpr hq

/-- **KP Proposition A.5.19(3), kernel.** -/
theorem congruenceLieInjectivity : CongruenceLieInjectivityStatement.{u} := by
  intro R K _ _ _ _ _ _ G _ M hM n m h hm
  exact ⟨M.congruenceLieHom_ker hM h hm, M.congruenceLieQuotientHom_injective hM h hm⟩

end Langlands.GroupScheme.IntegralModel
