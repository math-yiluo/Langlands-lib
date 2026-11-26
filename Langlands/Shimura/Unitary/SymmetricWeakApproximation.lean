import Langlands.Shimura.Unitary.FiniteScalarExtension
import Langlands.Global.GlobalCompletionWeakApproximation
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Topology.Algebra.Module.Basic

/-! # Weak approximation of symmetric elements at finite and infinite places -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global
open scoped TensorProduct

universe u v

section Vector

variable (E : Type u) [Field E] [NumberField E]
  (S : Finset (Langlands.Global.FinitePlace E)) (m : ℕ)

private theorem denseRange_completedVectors :
    DenseRange (fun x : Fin m → E =>
      ((fun w : NumberField.InfinitePlace E => fun j => algebraMap E w.Completion (x j)),
        fun p : S => fun j => algebraMap E (FiniteCompletion E p.val) (x j))) := by
  let P := (∀ w : NumberField.InfinitePlace E, w.Completion) ×
    (∀ p : S, FiniteCompletion E p.val)
  let transpose (x : Fin m → P) :=
    ((fun w j => (x j).1 w), fun p j => (x j).2 p)
  have hsurj : Function.Surjective transpose := fun x => ⟨fun j =>
    (fun w => x.1 w j, fun p => x.2 p j), rfl⟩
  have hcont : Continuous transpose :=
    (continuous_pi fun w => continuous_pi fun j =>
      (continuous_apply w).comp (continuous_fst.comp (continuous_apply j))).prodMk
      (continuous_pi fun p => continuous_pi fun j =>
        (continuous_apply p).comp (continuous_snd.comp (continuous_apply j)))
  exact hsurj.denseRange.comp (DenseRange.piMap fun _ : Fin m =>
    denseRange_numberFieldFiniteCompletionDiagonal E S) hcont

end Vector

section Symmetry

variable {E : Type u} [Field E] [NumberField E] {A : Type v} [Ring A] [Algebra E A]
  {m : ℕ} (σ : AlgebraInvolution E A) (B : Module.Basis (Fin m) E A)

private def average : A →ₗ[E] A := (1 / 2 : E) • (LinearMap.id + σ.linear)

omit [NumberField E] in
private theorem average_fixed (a : A) : σ (average σ a) = average σ a := by
  change σ ((1 / 2 : E) • (a + σ a)) = (1 / 2 : E) • (a + σ a)
  rw [σ.apply_smul, σ.apply_add, σ.apply_apply, add_comm]

private theorem average_baseChange_eq_of_fixed (L : Type u) [Field L] [Algebra E L]
    {x : L ⊗[E] A} (hx : σ.baseChange L x = x) : (average σ).baseChange L x = x := by
  rw [average, LinearMap.baseChange_smul, LinearMap.baseChange_add, LinearMap.baseChange_id]
  change (1 / 2 : E) • (x + σ.baseChange L x) = x
  rw [hx, ← two_smul E, smul_smul, show (1 / 2 : E) * 2 = 1 by norm_num, one_smul]

private def averageInCoordinates (L : Type u) [Field L] [Algebra E L] :
    (Fin m → L) →ₗ[L] (Fin m → L) :=
  (B.baseChange L).equivFun.toLinearMap.comp
    (((average σ).baseChange L).comp (B.baseChange L).equivFun.symm.toLinearMap)

private theorem continuous_coordinateMap (L : Type u) [Field L] [TopologicalSpace L]
    [IsTopologicalRing L] (T : (Fin m → L) →ₗ[L] (Fin m → L)) : Continuous T := by
  have h (x : Fin m → L) : T x = ∑ i, x i • T (Pi.single i 1) := by
    simp only [← map_smul, ← map_sum]
    congr 1
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · simp
  rw [show (T : (Fin m → L) → (Fin m → L)) = (fun x => ∑ i, x i • T (Pi.single i 1)) from
    funext h]
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).smul continuous_const)

omit [NumberField E] in
private theorem averageInCoordinates_tmul (L : Type u) [Field L] [Algebra E L]
    (a : A) : averageInCoordinates σ B L (fun j => algebraMap E L (B.equivFun a j)) =
      (B.baseChange L).equivFun (1 ⊗ₜ[E] average σ a) := by
  have h : (B.baseChange L).equivFun ((1 : L) ⊗ₜ[E] a) =
      fun j => algebraMap E L (B.equivFun a j) := by
    funext j
    change (B.baseChange L).repr ((1 : L) ⊗ₜ[E] a) j = algebraMap E L (B.repr a j)
    rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  rw [← h]
  change (B.baseChange L).equivFun ((average σ).baseChange L
    ((B.baseChange L).equivFun.symm ((B.baseChange L).equivFun _))) = _
  rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]

variable (S : Finset (Langlands.Global.FinitePlace E))
  (U : ∀ p : S, Set (Fin m → FiniteCompletion E p.val))
  (V : ∀ w : NumberField.InfinitePlace E, Set (Fin m → w.Completion))

private theorem exists_symmetric_with_coordinates
    (hU : ∀ p, IsOpen (U p)) (hV : ∀ w, IsOpen (V w))
    (hU₀ : ∀ p : S, ∃ x : FiniteCompletion E p.val ⊗[E] A,
      σ.baseChange (FiniteCompletion E p.val) x = x ∧
        (B.baseChange (FiniteCompletion E p.val)).equivFun x ∈ U p)
    (hV₀ : ∀ w : NumberField.InfinitePlace E, ∃ x : w.Completion ⊗[E] A,
      σ.baseChange w.Completion x = x ∧ (B.baseChange w.Completion).equivFun x ∈ V w) :
    ∃ a : A, σ a = a ∧
      (∀ p : S, (B.baseChange (FiniteCompletion E p.val)).equivFun (1 ⊗ₜ[E] a) ∈ U p) ∧
      (∀ w : NumberField.InfinitePlace E, (B.baseChange w.Completion).equivFun (1 ⊗ₜ[E] a) ∈ V w) := by
  let U' (p : S) := averageInCoordinates σ B (FiniteCompletion E p.val) ⁻¹' U p
  let V' (w : NumberField.InfinitePlace E) := averageInCoordinates σ B w.Completion ⁻¹' V w
  have hU' (p : S) : IsOpen (U' p) := (hU p).preimage (continuous_coordinateMap _ _)
  have hV' (w : NumberField.InfinitePlace E) : IsOpen (V' w) :=
    (hV w).preimage (continuous_coordinateMap _ _)
  have nonempty_preimage (L : Type u) [Field L] [Algebra E L] (O : Set (Fin m → L))
      (hO : ∃ x : L ⊗[E] A, σ.baseChange L x = x ∧ (B.baseChange L).equivFun x ∈ O) :
      (averageInCoordinates σ B L ⁻¹' O).Nonempty := by
    obtain ⟨x, hx, hmem⟩ := hO
    refine ⟨(B.baseChange L).equivFun x, ?_⟩
    change (B.baseChange L).equivFun ((average σ).baseChange L
      ((B.baseChange L).equivFun.symm ((B.baseChange L).equivFun x))) ∈ O
    rwa [LinearEquiv.symm_apply_apply, average_baseChange_eq_of_fixed σ L hx]
  have hbox := (isOpen_set_pi Set.finite_univ (fun w _ => hV' w)).prod
    (isOpen_set_pi Set.finite_univ (fun p _ => hU' p))
  have hbox₀ : ((Set.pi Set.univ V') ×ˢ (Set.pi Set.univ U')).Nonempty :=
    (Set.univ_pi_nonempty_iff.mpr (fun w => nonempty_preimage _ _ (hV₀ w))).prod
      (Set.univ_pi_nonempty_iff.mpr (fun p => nonempty_preimage _ _ (hU₀ p)))
  obtain ⟨x, hx⟩ := (denseRange_completedVectors E S m).exists_mem_open hbox hbox₀
  let b := B.equivFun.symm x
  have hb (j : Fin m) : B.equivFun b j = x j := congrFun (B.equivFun.apply_symm_apply x) j
  refine ⟨average σ b, average_fixed σ b, fun p => ?_, fun w => ?_⟩
  · have hp := hx.2 p (Set.mem_univ _)
    change averageInCoordinates σ B (FiniteCompletion E p.val)
      (fun j => algebraMap E (FiniteCompletion E p.val) (x j)) ∈ U p at hp
    simpa only [← hb, averageInCoordinates_tmul] using hp
  · have hw := hx.1 w (Set.mem_univ _)
    change averageInCoordinates σ B w.Completion
      (fun j => algebraMap E w.Completion (x j)) ∈ V w at hw
    simpa only [← hb, averageInCoordinates_tmul] using hw

/-- Nonempty open conditions in completed basis coordinates that contain
local symmetric points are attained by a single global symmetric element. -/
def symmetricWeakApproximation
    (hU : ∀ p, IsOpen (U p)) (hV : ∀ w, IsOpen (V w))
    (hU₀ : ∀ p : S, ∃ x : FiniteCompletion E p.val ⊗[E] A,
      σ.baseChange (FiniteCompletion E p.val) x = x ∧
        (B.baseChange (FiniteCompletion E p.val)).equivFun x ∈ U p)
    (hV₀ : ∀ w : NumberField.InfinitePlace E, ∃ x : w.Completion ⊗[E] A,
      σ.baseChange w.Completion x = x ∧ (B.baseChange w.Completion).equivFun x ∈ V w) :
    {a : A // σ a = a ∧
      (∀ p : S, (B.baseChange (FiniteCompletion E p.val)).equivFun (1 ⊗ₜ[E] a) ∈ U p) ∧
      (∀ w : NumberField.InfinitePlace E, (B.baseChange w.Completion).equivFun (1 ⊗ₜ[E] a) ∈ V w)} :=
  let h := exists_symmetric_with_coordinates σ B S U V hU hV hU₀ hV₀
  ⟨h.choose, h.choose_spec⟩

end Symmetry

end Langlands.Shimura.FiniteUnitary
