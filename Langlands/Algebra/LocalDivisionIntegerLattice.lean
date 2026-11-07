import Langlands.Algebra.LocalDivisionResidue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.Noetherian.Basic

/-! The original local division-algebra integer set as a finite base-integer lattice. -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel

universe u

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance latticeLocalNormedField : NontriviallyNormedField K := LocalGalois.localNormedField K
local instance latticeLocalCompleteSpace : CompleteSpace K := LocalGalois.localNormedField_complete K
local instance latticeLocalUltrametric : IsUltrametricDist K := LocalGalois.localNormedField_ultrametric K
local instance latticeIntegerAlgebra : Algebra 𝒪[K] D := Algebra.compHom D (algebraMap 𝒪[K] K)
local instance latticeIntegerTower : IsScalarTower 𝒪[K] K D := .of_algebraMap_smul (fun _ _ => rfl)

/-- The original integer set with the scalar action of the original base integer ring. -/
def localDivisionIntegerLattice : Submodule 𝒪[K] D where
  carrier := (localReducedNormValuation K D).integer
  zero_mem' := by simp
  add_mem' hx hy := (localReducedNormValuation K D).integer.add_mem hx hy
  smul_mem' c x hx := by
    change localReducedNormValuation K D x ≤ 1 at hx
    change localReducedNormValuation K D ((c : K) • x) ≤ 1
    rw [Algebra.smul_def, map_mul, localReducedNormValuation_algebraMap]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ zero_le c.prop) zero_le).trans
      (by simpa only [one_mul] using hx)

/-- The actual integer lattice spans the original division algebra over its base field. -/
theorem localDivisionIntegerLattice_span :
    Submodule.span K (localDivisionIntegerLattice K D : Set D) = ⊤ := by
  let := localDivisionNormedRing K D
  let := localDivisionNormedAlgebra K D
  apply top_unique
  intro x _
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K (‖x‖ + 1)
  have hcpos : 0 < ‖c‖ := (by positivity : (0 : ℝ) < ‖x‖ + 1).trans hc
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  have hy : c⁻¹ • x ∈ localDivisionIntegerLattice K D := by
    apply (localDivisionNorm_le_one_iff K D _).mp
    rw [norm_smul, norm_inv, ← div_eq_inv_mul]
    exact (div_le_one hcpos).mpr (le_trans (by linarith : ‖x‖ ≤ ‖x‖ + 1) hc.le)
  have hm := (Submodule.span K (localDivisionIntegerLattice K D : Set D)).smul_mem c
    (Submodule.subset_span hy)
  simpa only [smul_smul, mul_inv_cancel₀ hc0, one_smul] using hm

/-- Compactness bounds all original coordinates by one common nonzero base scalar. -/
theorem exists_localDivisionIntegerLattice_coordinate_bound :
    letI := localDivisionNormedRing K D
    letI := localDivisionNormedAlgebra K D
    ∃ c : K, c ≠ 0 ∧ ∀ x : localDivisionIntegerLattice K D,
      ∀ i : Fin (Module.finrank K D),
        valuation K ((Module.finBasis K D).equivFun x.val i / c) ≤ 1 := by
  let := localDivisionNormedRing K D
  let := localDivisionNormedAlgebra K D
  let b := Module.finBasis K D
  have hb := ((localDivisionInteger_isCompact K D).image b.equivFunL.continuous).isBounded
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K (max C 0)
  have hcpos : 0 < ‖c‖ := (le_max_right C 0).trans_lt hc
  refine ⟨c, norm_pos_iff.mp hcpos, fun x i => ?_⟩
  have hx : ‖b.equivFun x.val‖ ≤ C := hC _ ⟨x.val, x.prop, rfl⟩
  have hxi : ‖b.equivFun x.val i‖ ≤ C := (norm_le_pi_norm _ i).trans hx
  have hn : ‖b.equivFun x.val i / c‖ ≤ ‖(1 : K)‖ := by
    rw [norm_div, norm_one]
    exact (div_le_one hcpos).mpr (hxi.trans ((le_max_left C 0).trans hc.le))
  simpa only [map_one] using (LocalGalois.localNormedField_le K _ 1).mp hn

/-- The actual integer lattice is finite over the original base integer ring. -/
theorem localDivisionIntegerLattice_finite :
    Module.Finite 𝒪[K] (localDivisionIntegerLattice K D) := by
  let := localDivisionNormedRing K D
  let := localDivisionNormedAlgebra K D
  obtain ⟨c, hc0, hc⟩ := exists_localDivisionIntegerLattice_coordinate_bound K D
  let b := Module.finBasis K D
  let ψ : localDivisionIntegerLattice K D →ₗ[𝒪[K]]
      (Fin (Module.finrank K D) → 𝒪[K]) :=
    { toFun := fun x i => ⟨b.equivFun x.val i / c, hc x i⟩
      map_add' := by
        intro x y
        funext i
        apply Subtype.ext
        change b.equivFun (x.val + y.val) i / c =
          b.equivFun x.val i / c + b.equivFun y.val i / c
        simp only [map_add, Pi.add_apply, add_div]
      map_smul' := by
        intro a x
        funext i
        apply Subtype.ext
        change b.equivFun ((a : K) • x.val) i / c = (a : K) * _
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc] }
  apply Module.Finite.of_injective ψ
  intro x y h
  apply Subtype.ext
  apply b.equivFun.injective
  funext i
  have hi := congrArg (fun z : Fin (Module.finrank K D) → 𝒪[K] => (z i : K)) h
  change b.equivFun x.val i / c = b.equivFun y.val i / c at hi
  exact (div_left_inj' hc0).mp hi

end Langlands.CentralDivision
