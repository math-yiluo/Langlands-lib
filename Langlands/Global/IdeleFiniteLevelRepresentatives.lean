import Langlands.Automorphic.RankOneDeterminantBand

/-! # Finite idele representatives modulo principal ideles and finite level -/

noncomputable section

universe u

open NumberField
open scoped Classical NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

variable (F : Type u) [Field F] [NumberField F]

private theorem finite_normSection (h : ℝ≥0ˣ) :
    ((ideleProductEquiv F) (IdeleAbsoluteValue.normSection F h)).2 = 1 := by
  change ((ideleProductEquiv F) ((ideleProductEquiv F).symm (_, 1))).2 = 1
  rw [ContinuousMulEquiv.apply_symm_apply]

/-- Finitely many ideles suffice modulo principal ideles, the infinite part,
and any prescribed open subgroup of the finite ideles. -/
theorem exists_finiteIdeleLevelRepresentatives (U : OpenSubgroup (FiniteIdeles F)) :
    ∃ T : Finset (Ideles F), ∀ z : Ideles F, ∃ r ∈ T, ∃ (a : Fˣ) (x : (InfiniteAdeles F)ˣ)
      (v : FiniteIdeles F), v ∈ U ∧
        z = diagonalUnits F a * r * (infiniteIdelesInclusion F x * finiteIdelesInclusion F v) := by
  obtain ⟨C, hC, -, hcover⟩ := NormOneIdeleClass.exists_isCompact_fundamentalSet F
  let e := ideleProductEquiv F
  let π (z : Ideles F) := (e z).2
  let O (r : Ideles F) := {z : Ideles F | (π r)⁻¹ * π z ∈ U}
  have hp : Continuous π := continuous_snd.comp e.continuous
  have hn (r : Ideles F) : O r ∈ 𝓝 r := by
    have ho : IsOpen (O r) := U.isOpen.preimage (hp.const_mul _)
    refine ho.mem_nhds ?_
    change (π r)⁻¹ * π r ∈ U
    rw [inv_mul_cancel]
    exact U.one_mem
  obtain ⟨T, -, hT⟩ := hC.elim_nhds_subcover O (fun r _ => hn r)
  refine ⟨T, ?_⟩
  intro z
  let s := IdeleAbsoluteValue.normSection F (IdeleAbsoluteValue.full F z)
  have hz : z * s⁻¹ ∈ NormOneIdeleClass.normOneIdeles F := by
    change IdeleAbsoluteValue.full F (z * s⁻¹) = 1
    simp only [map_mul, map_inv, s, IdeleAbsoluteValue.full_normSection, mul_inv_cancel]
  obtain ⟨a, ha⟩ := hcover _ hz
  have ha' : diagonalUnits F a * (z * s⁻¹) ∈ ⋃ r ∈ T, O r := hT ha
  obtain ⟨r, hr, hmem⟩ := Set.mem_iUnion₂.mp ha'
  let w := r⁻¹ * (diagonalUnits F a * z)
  have hm : (e w).2 ∈ U := by
    change (π r)⁻¹ * π (diagonalUnits F a * (z * s⁻¹)) ∈ U at hmem
    have hs : (e s).2 = 1 := finite_normSection F _
    simpa only [π, map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, hs, inv_one, mul_one, w] using hmem
  refine ⟨r, hr, a⁻¹, (e w).1, (e w).2, hm, ?_⟩
  have hw : infiniteIdelesInclusion F (e w).1 * finiteIdelesInclusion F (e w).2 = w := by
    apply e.injective
    rw [map_mul]
    change e (e.symm ((e w).1, 1)) * e (e.symm (1, (e w).2)) = e w
    rw [e.apply_symm_apply, e.apply_symm_apply]
    exact Prod.ext (mul_one _) (one_mul _)
  rw [hw, map_inv]
  dsimp [w]
  group

/-- A chosen finite set of representatives at the specified open finite level. -/
def finiteIdeleLevelRepresentatives (U : OpenSubgroup (FiniteIdeles F)) : Finset (Ideles F) :=
  (exists_finiteIdeleLevelRepresentatives F U).choose

theorem finiteIdeleLevelRepresentatives_spec (U : OpenSubgroup (FiniteIdeles F)) (z : Ideles F) :
    ∃ r ∈ finiteIdeleLevelRepresentatives F U, ∃ (a : Fˣ) (x : (InfiniteAdeles F)ˣ)
      (v : FiniteIdeles F), v ∈ U ∧
        z = diagonalUnits F a * r * (infiniteIdelesInclusion F x * finiteIdelesInclusion F v) :=
  (exists_finiteIdeleLevelRepresentatives F U).choose_spec z

end Langlands.Global
