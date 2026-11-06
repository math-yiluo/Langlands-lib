import Langlands.GroupScheme.SplitExistence.IntegralBase
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.Tactic

/-! # Bases of finite reduced integral root data -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

open Set Function IsAddIndecomposable

namespace Langlands.LinearAlgebra.RootDatumBase

private theorem exists_regular_on_finset {J M : Type*} [AddCommGroup M]
    (f : J → M →+ ℤ) (s : Finset J) (hf : ∀ i ∈ s, ∃ x, f i x ≠ 0) :
    ∃ x, ∀ i ∈ s, f i x ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert j s hj ih =>
    obtain ⟨x, hx⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨y, hy⟩ := hf j (Finset.mem_insert_self _ _)
    have hbad (i : J) (hi : i ∈ insert j s) :
        {n : ℤ | f i (x + n • y) = 0}.Finite := by
      by_cases hiy : f i y = 0
      · have his : i ∈ s := by
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact False.elim (hy hiy)
          · exact hi
        simp [map_add, map_zsmul, hiy, hx i his]
      · apply Set.Subsingleton.finite
        intro a ha b hb
        simp only [Set.mem_ofPred_eq, map_add, map_zsmul, zsmul_eq_mul, Int.cast_id] at ha hb
        exact mul_right_cancel₀ hiy (by linarith : a * f i y = b * f i y)
    obtain ⟨n, hn⟩ := ((insert j s).finite_toSet.biUnion hbad).exists_notMem
    refine ⟨x + n • y, fun i hi hzero => hn ?_⟩
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hzero⟩⟩

variable {J M N : Type*} [Finite J] [AddCommGroup M] [AddCommGroup N]
    (P : RootDatum J M N)

/-- A finite integral root datum has an integral functional regular on every root. -/
theorem exists_regular_functional :
    ∃ f : Module.Dual ℤ M, ∀ i, f (P.root i) ≠ 0 := by
  classical
  let := Fintype.ofFinite J
  obtain ⟨y, hy⟩ := exists_regular_on_finset
    (fun i => (P.root' i).toAddMonoidHom) Finset.univ
    (fun i _ => ⟨P.coroot i, by simp⟩)
  exact ⟨P.flip.toLinearMap y, fun i => hy i (Finset.mem_univ i)⟩

variable [P.IsReduced]

/-- Matching positive root and coroot signs give the same indecomposable indices,
without a spanning hypothesis. -/
theorem baseOf_root_eq_baseOf_coroot
    (f : Module.Dual ℤ M) (g : Module.Dual ℤ N)
    (hf : ∀ i, f (P.root i) ≠ 0) (hg : ∀ i, g (P.coroot i) ≠ 0)
    (hfg : ∀ i, 0 < f (P.root i) ↔ 0 < g (P.coroot i)) :
    baseOf P.root (f : M →+ ℤ) = baseOf P.coroot (g : N →+ ℤ) := by
  letI := Fintype.ofFinite J
  exact Langlands.GroupScheme.SplitExistence.baseOf_root_eq_baseOf_coroot P f g hf hg hfg

/-- A finite reduced datum has a base on its original integral modules. -/
theorem nonempty_base : Nonempty P.Base :=
  Langlands.GroupScheme.SplitExistence.nonempty_base_int P

/-- A chosen base on the original integral modules. -/
noncomputable def base : P.Base := Classical.choice (nonempty_base P)

end Langlands.LinearAlgebra.RootDatumBase
