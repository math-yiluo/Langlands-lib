import Langlands.Topology.Rationalization.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.Algebra.Group.Torsion
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ZPow
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Compactness.LocallyCompact

open scoped TensorProduct
open Topology

namespace Langlands.Topology.Rationalization

universe u
variable {M : Type u} [AddCommGroup M]

private theorem integral_injective [IsAddTorsionFree M] :
    Function.Injective (fun x : M => (1 : ℚ) ⊗ₜ[ℤ] x) := by
  apply (IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ M 1)).2
  intro c
  exact zsmul_right_injective (mem_nonZeroDivisors_iff_ne_zero.mp c.property)

/-- Every rationalized element lies in a chart with nonzero rational coefficient. -/
theorem exists_chart (z : ℚ ⊗[ℤ] M) :
    ∃ (q : ℚ), q ≠ 0 ∧ ∃ x : M, q ⊗ₜ[ℤ] x = z := by
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ M 1) z
  have hs0 : (s.val : ℚ) ≠ 0 := by
    exact_mod_cast (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
  refine ⟨(s.val : ℚ)⁻¹, inv_ne_zero hs0, m, ?_⟩
  have hs' : (s.val : ℚ) • z = (1 : ℚ) ⊗ₜ[ℤ] m := by
    simpa only [Submonoid.smul_def, TensorProduct.mk_apply, Int.cast_smul_eq_zsmul] using hs
  calc
    (s.val : ℚ)⁻¹ ⊗ₜ[ℤ] m = (s.val : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] m) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = z := by rw [← hs', inv_smul_smul₀ hs0]

private theorem tmul_eq_integral_iff [IsAddTorsionFree M] (q : ℚ) (x y : M) :
    q ⊗ₜ[ℤ] x = (1 : ℚ) ⊗ₜ[ℤ] y ↔ q.num • x = q.den • y := by
  have hn : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  rw [← (smul_right_injective (M := ℚ ⊗[ℤ] M) hn).eq_iff]
  have hleft : (q.den : ℚ) • (q ⊗ₜ[ℤ] x) = (1 : ℚ) ⊗ₜ[ℤ] (q.num • x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_comm, Rat.mul_den_eq_num]
    simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul, mul_one]
  have hright : (q.den : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] y) =
      (1 : ℚ) ⊗ₜ[ℤ] (q.den • y) := by
    simp [TensorProduct.smul_tmul', smul_eq_mul]
  rw [hleft, hright, integral_injective.eq_iff]

private theorem exists_common_chart (z w : ℚ ⊗[ℤ] M) :
    ∃ (q : ℚ), q ≠ 0 ∧ ∃ x y : M, q ⊗ₜ[ℤ] x = z ∧ q ⊗ₜ[ℤ] y = w := by
  let f := TensorProduct.mk ℤ ℚ M (1 : ℚ)
  obtain ⟨s, hs⟩ := IsLocalizedModule.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) f (fun b : Bool => if b then z else w)
  obtain ⟨x, hx⟩ := hs true
  obtain ⟨y, hy⟩ := hs false
  have hs0 : (s.val : ℚ) ≠ 0 := by
    exact_mod_cast (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
  have hz : (1 : ℚ) ⊗ₜ[ℤ] x = (s.val : ℚ) • z := by
    simpa only [f, TensorProduct.mk_apply, ↓reduceIte, Int.cast_smul_eq_zsmul] using hx
  have hw : (1 : ℚ) ⊗ₜ[ℤ] y = (s.val : ℚ) • w := by
    simpa only [f, TensorProduct.mk_apply, Bool.false_eq_true, ↓reduceIte,
      Int.cast_smul_eq_zsmul] using hy
  refine ⟨(s.val : ℚ)⁻¹, inv_ne_zero hs0, x, y, ?_, ?_⟩
  · simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, inv_smul_smul₀ hs0] using
      congrArg (fun a : ℚ ⊗[ℤ] M => (s.val : ℚ)⁻¹ • a) hz
  · simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, inv_smul_smul₀ hs0] using
      congrArg (fun a : ℚ ⊗[ℤ] M => (s.val : ℚ)⁻¹ • a) hw

section Topology
variable [TopologicalSpace M]

local instance : TopologicalSpace (ℚ ⊗[ℤ] M) := finalTopology M

/-- Multiplication by a nonzero rational, with the final topology on both sides. -/
def scalarHomeomorph (q : ℚ) (hq : q ≠ 0) :
    (ℚ ⊗[ℤ] M) ≃ₜ (ℚ ⊗[ℤ] M) where
  toFun z := q • z
  invFun z := q⁻¹ • z
  left_inv z := inv_smul_smul₀ hq z
  right_inv z := smul_inv_smul₀ hq z
  continuous_toFun := Rationalization.continuous_smul q
  continuous_invFun := Rationalization.continuous_smul q⁻¹

@[simp] theorem scalarHomeomorph_apply (q : ℚ) (hq : q ≠ 0) (z : ℚ ⊗[ℤ] M) :
    scalarHomeomorph q hq z = q • z := rfl

@[simp] theorem scalarHomeomorph_symm_apply (q : ℚ) (hq : q ≠ 0) (z : ℚ ⊗[ℤ] M) :
    (scalarHomeomorph q hq).symm z = q⁻¹ • z := rfl

variable [IsTopologicalAddGroup M]
  (hM : ∀ n : ℕ, 0 < n → IsOpenEmbedding (fun x : M => n • x))

include hM in
/-- The integral chart identifies `M` with an open subspace of its rationalization. -/
theorem isOpenEmbedding_integral :
    IsOpenEmbedding (fun x : M => (1 : ℚ) ⊗ₜ[ℤ] x) := by
  let : IsAddTorsionFree M := ⟨fun n hn => (hM n (Nat.pos_of_ne_zero hn)).injective⟩
  have hcont : Continuous (fun x : M => (1 : ℚ) ⊗ₜ[ℤ] x) := by
    exact Rationalization.continuous_tmul (M := M) 1
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap hcont integral_injective
  intro U hU
  apply isOpen_finalTopology_iff.2
  intro q
  have heq : (fun x : M => q ⊗ₜ[ℤ] x) ⁻¹' ((fun x : M => (1 : ℚ) ⊗ₜ[ℤ] x) '' U) =
      (fun x : M => q.num • x) ⁻¹' ((fun x : M => q.den • x) '' U) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, ((tmul_eq_integral_iff q x y).1 hxy.symm).symm⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, ((tmul_eq_integral_iff q x y).2 hxy.symm).symm⟩
  rw [heq]
  exact ((hM q.den q.den_pos).isOpenMap U hU).preimage (continuous_id.const_smul q.num)

include hM in
/-- Every nonzero rational chart is an open embedding for the final topology. -/
theorem isOpenEmbedding_chart (q : ℚ) (hq : q ≠ 0) :
    IsOpenEmbedding (fun x : M => q ⊗ₜ[ℤ] x) := by
  have h := (scalarHomeomorph q hq).isOpenEmbedding.comp
    (isOpenEmbedding_integral hM)
  change IsOpenEmbedding (fun x : M => q • ((1 : ℚ) ⊗ₜ[ℤ] x)) at h
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h

include hM in
/-- Addition and negation are continuous for the final topology. Install locally. -/
theorem topologicalAddGroup : IsTopologicalAddGroup (ℚ ⊗[ℤ] M) where
  continuous_add := by
    apply continuous_iff_continuousAt.2
    rintro ⟨z, w⟩
    obtain ⟨q, hq, x, y, rfl, rfl⟩ := exists_common_chart z w
    apply (((isOpenEmbedding_chart hM q hq).prodMap
      (isOpenEmbedding_chart hM q hq)).continuousAt_iff (x := (x, y))).mp
    have hc := (Rationalization.continuous_tmul (M := M) q).comp (continuous_fst.add continuous_snd :
      Continuous (fun p : M × M => p.1 + p.2))
    simpa only [Function.comp_def, Pi.add_apply, Prod.map, TensorProduct.tmul_add] using hc.continuousAt
  continuous_neg := by
    apply continuous_of_forall_continuous_tmul
    intro q
    have hc := (Rationalization.continuous_tmul (M := M) q).comp continuous_neg
    simpa only [Function.comp_def, TensorProduct.tmul_neg] using hc

include hM in
/-- Hausdorffness of the lattice passes to its rationalization. Install locally. -/
theorem hausdorff [T2Space M] : T2Space (ℚ ⊗[ℤ] M) := by
  let := topologicalAddGroup hM
  apply IsTopologicalAddGroup.t2Space_iff_zero_closed.mpr
  rw [← isOpen_compl_iff]
  apply isOpen_finalTopology_iff.2
  intro q
  by_cases hq : q = 0
  · subst q
    simp
  · have hinj := (isOpenEmbedding_chart hM q hq).injective
    have heq : (fun x : M => q ⊗ₜ[ℤ] x) ⁻¹' ({0} : Set (ℚ ⊗[ℤ] M)) = {0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      rw [← TensorProduct.tmul_zero M q, hinj.eq_iff]
    rw [Set.preimage_compl, heq]
    exact isOpen_compl_singleton

include hM in
/-- A compact lattice has compact open image in its rationalization. -/
theorem compactOpen_integral [CompactSpace M] :
    IsCompact (Set.range (fun x : M => (1 : ℚ) ⊗ₜ[ℤ] x)) ∧
      IsOpen (Set.range (fun x : M => (1 : ℚ) ⊗ₜ[ℤ] x)) :=
  ⟨isCompact_range (Rationalization.continuous_tmul (M := M) 1),
    (isOpenEmbedding_integral hM).isOpen_range⟩

include hM in
/-- A compact lattice gives a locally compact rationalization. Install locally. -/
theorem locallyCompact [CompactSpace M] : LocallyCompactSpace (ℚ ⊗[ℤ] M) := by
  let := topologicalAddGroup hM
  have hc := isCompact_range (Rationalization.continuous_tmul (M := M) (1 : ℚ))
  exact hc.locallyCompactSpace_of_mem_nhds_of_addGroup
    ((isOpenEmbedding_integral hM).isOpen_range.mem_nhds
      (show (0 : ℚ ⊗[ℤ] M) ∈ Set.range (fun x : M => (1 : ℚ) ⊗ₜ[ℤ] x) from
        ⟨0, by simp⟩))

end Topology

section Action
variable {Γ : Type*} [Group Γ] [DistribMulAction Γ M]

/-- The existing algebraic rational scalar extension of the action of `g`. -/
def actionMap (g : Γ) : ℚ ⊗[ℤ] M →ₗ[ℚ] ℚ ⊗[ℤ] M :=
  (DistribSMul.toAddMonoidHom M g).toIntLinearMap.baseChange ℚ

@[simp] theorem actionMap_tmul (g : Γ) (q : ℚ) (x : M) :
    actionMap g (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] (g • x) := rfl

@[simp] theorem actionMap_one (z : ℚ ⊗[ℤ] M) : actionMap (1 : Γ) z = z := by
  induction z using TensorProduct.inductionOn with
  | tmul q x => simp
  | add z w hz hw => simp_all

theorem actionMap_mul (g k : Γ) (z : ℚ ⊗[ℤ] M) :
    actionMap (g * k) z = actionMap g (actionMap k z) := by
  induction z using TensorProduct.inductionOn with
  | tmul q x => simp [mul_smul]
  | add z w hz hw => simp_all

/-- The rationalized additive action, available for local installation. -/
@[instance_reducible] def rationalAction : DistribMulAction Γ (ℚ ⊗[ℤ] M) where
  smul := fun g x => actionMap (M := M) g x
  one_smul := actionMap_one (M := M)
  mul_smul := actionMap_mul (M := M)
  smul_zero g := map_zero (actionMap (M := M) g)
  smul_add g := map_add (actionMap (M := M) g)

theorem rationalAction_smul (g : Γ) (z : ℚ ⊗[ℤ] M) :
    letI := rationalAction (M := M) (Γ := Γ)
    g • z = (DistribSMul.toAddMonoidHom M g).toIntLinearMap.baseChange ℚ z := rfl

theorem rationalAction_tmul (g : Γ) (q : ℚ) (x : M) :
    letI := rationalAction (M := M) (Γ := Γ)
    g • (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] (g • x) := rfl

variable [TopologicalSpace M] [IsTopologicalAddGroup M]
  (hM : ∀ n : ℕ, 0 < n → IsOpenEmbedding (fun x : M => n • x))

local instance : TopologicalSpace (ℚ ⊗[ℤ] M) := finalTopology M

variable [TopologicalSpace Γ] [ContinuousSMul Γ M]

include hM in
/-- Joint continuity of the rational scalar extensions for the final topology. -/
theorem continuous_actionMap :
    Continuous (fun p : Γ × (ℚ ⊗[ℤ] M) => actionMap p.1 p.2) := by
  apply continuous_iff_continuousAt.2
  rintro ⟨g, z⟩
  obtain ⟨q, hq, x, rfl⟩ := exists_chart z
  apply ((IsOpenEmbedding.id.prodMap (isOpenEmbedding_chart hM q hq)).continuousAt_iff
    (x := (g, x))).mp
  have hc := (Rationalization.continuous_tmul (M := M) q).comp
    (continuous_smul : Continuous (fun p : Γ × M => p.1 • p.2))
  simpa only [Function.comp_def, Prod.map, id_eq, actionMap_tmul] using hc.continuousAt

include hM in
/-- The locally installed rationalized action is jointly continuous. -/
theorem continuousSMul_rationalAction :
    letI := rationalAction (M := M) (Γ := Γ)
    ContinuousSMul Γ (ℚ ⊗[ℤ] M) := by
  let := rationalAction (M := M) (Γ := Γ)
  exact ⟨continuous_actionMap hM⟩
end Action

end Langlands.Topology.Rationalization
