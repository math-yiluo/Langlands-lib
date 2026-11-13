import Langlands.Sheaf.Renard.CoinvariantStatements

/-!
# Stalks of Renard's vector sheaf of a nondegenerate target-test module
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.FibreCoinvariantStalk

open CategoryTheory Opposite TopologicalSpace
open Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Renard.ProjectorBasisSheaf

variable {Y : Type} [TopologicalSpace Y] (hY : Langlands.Topology.IsLocallyProfinite Y)
  {M : Type} [AddCommGroup M] [NonUnitalModule (PointwiseTestAlgebra.Carrier Y) M]
  (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier Y) M) (y : Y)

/-- The germ at `y` of Renard's original-vector global section `(χ_U · m)_U`. -/
def stalkGerm :
    letI := ProjectorVectorSheaf.originalModule hM
    M →ₗ[ℂ] (ProjectorVectorSheaf.presheaf.{0,0} hY hM).stalk y :=
  letI := ProjectorVectorSheaf.originalModule hM
  ((ProjectorVectorSheaf.presheaf.{0,0} hY hM).Γgerm y).hom.comp
    (ProjectorVectorSheaf.originalSection.{0,0} hY hM ⊤)

theorem stalkGerm_apply (m : M) :
    stalkGerm hY hM y m = (ProjectorVectorSheaf.presheaf.{0,0} hY hM).Γgerm y
      (ProjectorVectorSheaf.originalSection.{0,0} hY hM ⊤ m) := rfl

/-- A compact open neighbourhood inside a given open neighbourhood. -/
theorem exists_compactOpen_le {U : Opens Y} (hyU : y ∈ U) :
    ∃ K : CompactOpen hY, y ∈ K.obj ∧ K.obj ≤ U := by
  obtain ⟨V, hyV, hVo, hVc, hVU⟩ :=
    hY.hasCompactOpenNeighborhoodBasis y U (U.isOpen.mem_nhds hyU)
  exact ⟨⟨⟨V, hVo⟩, hVc⟩, hyV, hVU⟩

/-- Every stalk element is the germ of an original-vector section. -/
theorem stalkGerm_surjective : Function.Surjective (stalkGerm hY hM y) := by
  intro t
  obtain ⟨U, hyU, s, rfl⟩ := (ProjectorVectorSheaf.presheaf.{0,0} hY hM).exists_germ_eq t
  obtain ⟨K, hyK, hKU⟩ := exists_compactOpen_le hY y hyU
  refine ⟨(s.val ⟨K, hKU⟩).val, ?_⟩
  have hres : ((ProjectorVectorSheaf.presheaf.{0,0} hY hM).map (homOfLE hKU).op).hom s =
      ProjectorVectorSheaf.originalSection.{0,0} hY hM K.obj (s.val ⟨K, hKU⟩).val := by
    apply ProjectorVectorSheaf.section_ext hY hM
    intro W
    exact (congrArg Subtype.val (ProjectorVectorSheaf.section_compatible hY hM s ⟨K, hKU⟩
      ⟨W.val, W.property.trans hKU⟩ W.property)).symm
  rw [stalkGerm_apply, ← TopCat.Presheaf.germ_res_apply (ProjectorVectorSheaf.presheaf.{0,0} hY hM)
      (homOfLE hKU) y hyK s, hres,
    ← TopCat.Presheaf.Γgerm_res_apply (ProjectorVectorSheaf.presheaf.{0,0} hY hM)
      (i := homOfLE (le_top : K.obj ≤ ⊤)) y hyK]
  rfl

/-- The kernel of the stalk germ: some compact-open neighbourhood test kills the vector. -/
theorem stalkGerm_eq_zero_iff (m : M) :
    stalkGerm hY hM y m = 0 ↔ ∃ K : CompactOpen hY, y ∈ K.obj ∧ action hY M K m = 0 := by
  constructor
  · intro h
    rw [stalkGerm_apply, ← map_zero ((ProjectorVectorSheaf.presheaf.{0,0} hY hM).Γgerm y).hom]
      at h
    obtain ⟨W, hyW, iU, iV, hW⟩ :=
      (ProjectorVectorSheaf.presheaf.{0,0} hY hM).germ_eq (U := ⊤) (V := ⊤) y trivial trivial _ _ h
    obtain ⟨K, hyK, hKW⟩ := exists_compactOpen_le hY y hyW
    refine ⟨K, hyK, ?_⟩
    rw [map_zero] at hW
    have := congrArg (fun s : (ProjectorVectorSheaf.presheaf.{0,0} hY hM).obj (op W) =>
      (s.val ⟨K, hKW⟩).val) hW
    exact this
  · rintro ⟨K, hyK, hK⟩
    have hzero : ProjectorVectorSheaf.originalSection.{0,0} hY hM K.obj m = 0 := by
      apply ProjectorVectorSheaf.section_ext hY hM
      intro W
      change action hY M W.val m = 0
      rw [← action_absorb hY M W.property m, hK, map_zero]
    rw [stalkGerm_apply, ← TopCat.Presheaf.Γgerm_res_apply
      (ProjectorVectorSheaf.presheaf.{0,0} hY hM) (i := homOfLE (le_top : K.obj ≤ ⊤)) y hyK]
    erw [ProjectorVectorSheaf.originalSection_restrict hY hM (homOfLE (le_top : K.obj ≤ ⊤)) m,
      hzero]
    exact map_zero _

end Langlands.Sheaf.Renard.FibreCoinvariantStalk
