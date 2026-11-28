import Langlands.Algebra.CentralSimple.LandherrLocalTarget

/-! # Continuity of elementary products in coordinates -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.Quaternionic Langlands.BinaryElementary Filter Topology
open scoped TensorProduct

universe u

section Products

variable {R : Type u} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_upper_val : Continuous (fun p : R => (upper p : Matrix (Fin 2) (Fin 2) R)) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [continuous_const] <;> exact continuous_id

theorem continuous_lower_val : Continuous (fun p : R => (lower p : Matrix (Fin 2) (Fin 2) R)) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [continuous_const] <;> exact continuous_id

/-- The matrix of an elementary product depends continuously on its entries. -/
theorem continuous_listProd_ofFn (L : ℕ) :
    Continuous (fun g : Fin L → R × R => (listProd (List.ofFn g) : Matrix (Fin 2) (Fin 2) R)) := by
  induction L with
  | zero =>
    simp only [List.ofFn_zero, listProd_nil, Units.val_one]
    exact continuous_const
  | succ L ih =>
    simp only [List.ofFn_succ, listProd_cons, Units.val_mul]
    refine ((continuous_upper_val.comp ((continuous_apply 0).fst)).mul
      (continuous_lower_val.comp ((continuous_apply 0).snd))).mul ?_
    exact ih.comp (continuous_pi fun i => continuous_apply i.succ)

end Products

section Defs

variable {k : Type u} [Field k]
  (F : Type u) [Field F] [Algebra F k] (B : Type u) [Ring B] [Algebra F B]
  (τ : FirstKindInvolution F B) {ι : Type*} [Fintype ι] (β : Module.Basis ι F B)

/-- The matrix `t D τ(t)ᵗ` for the elementary product `t` with entries `g`. -/
def targetMap (D : Matrix (Fin 2) (Fin 2) (k ⊗[F] B)) {L : ℕ}
    (g : Fin L → (k ⊗[F] B) × (k ⊗[F] B)) : Matrix (Fin 2) (Fin 2) (k ⊗[F] B) :=
  (listProd (List.ofFn g) : Matrix (Fin 2) (Fin 2) (k ⊗[F] B)) * D *
    (τ.baseChange k).matrix (Fin 2) (listProd (List.ofFn g) : Matrix (Fin 2) (Fin 2) (k ⊗[F] B))

/-- Entries given by coordinates in the basis `1 ⊗ β`. -/
def coordPoint {L : ℕ} (c : Fin L × Fin 2 × ι → k) : Fin L → (k ⊗[F] B) × (k ⊗[F] B) :=
  fun j => (∑ i, c (j, 0, i) • ((1 : k) ⊗ₜ[F] β i), ∑ i, c (j, 1, i) • ((1 : k) ⊗ₜ[F] β i))

/-- The coordinates of a list of entries in the basis `1 ⊗ β`. -/
def coordOf {L : ℕ} (g : Fin L → (k ⊗[F] B) × (k ⊗[F] B)) : Fin L × Fin 2 × ι → k :=
  fun α => (Algebra.TensorProduct.basis k β).repr
    (if α.2.1 = 0 then (g α.1).1 else (g α.1).2) α.2.2

theorem coordPoint_coordOf {L : ℕ} (g : Fin L → (k ⊗[F] B) × (k ⊗[F] B)) :
    coordPoint F B β (coordOf F B β g) = g := by
  funext j
  have h : ∀ x : k ⊗[F] B, ∑ i, (Algebra.TensorProduct.basis k β).repr x i •
      ((1 : k) ⊗ₜ[F] β i) = x := fun x => by
    conv_rhs => rw [← (Algebra.TensorProduct.basis k β).sum_repr x]
    simp only [Algebra.TensorProduct.basis_apply]
  ext
  · simp only [coordPoint, coordOf]
    exact h _
  · simp only [coordPoint, coordOf, show ((1 : Fin 2) = 0) = False by decide, ite_false]
    exact h _

end Defs

variable {k : Type u} [NontriviallyNormedField k] [CompleteSpace k]
  (F : Type u) [Field F] [Algebra F k] (B : Type u) [Ring B] [Algebra F B] [FiniteDimensional F B]
  (τ : FirstKindInvolution F B) {ι : Type*} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F B)

/-- Let `B` be finite-dimensional over `F` and let `k` be a complete nontrivially normed
field over `F` with `2 ≠ 0`. If `t₀ D τ(t₀)ᵗ = 1` for the entries `g₀`, then throughout a
product of neighbourhoods of the coordinates of `g₀`, the matrix `t D τ(t)ᵗ` is a square in
the `k`-subalgebra it generates. -/
theorem exists_coord_nbhd (h2 : (2 : k) ≠ 0) (D : Matrix (Fin 2) (Fin 2) (k ⊗[F] B)) {L : ℕ}
    (g₀ : Fin L → (k ⊗[F] B) × (k ⊗[F] B)) (hg₀ : targetMap F B τ D g₀ = 1) :
    ∃ t : Fin L × Fin 2 × ι → Set k, (∀ α, t α ∈ 𝓝 (coordOf F B β g₀ α)) ∧
      ∀ c : Fin L × Fin 2 × ι → k, (∀ α, c α ∈ t α) →
        ∃ σ ∈ Algebra.adjoin k {targetMap F B τ D (coordPoint F B β c)},
          σ * σ = targetMap F B τ D (coordPoint F B β c) := by
  classical
  let _ : TopologicalSpace (k ⊗[F] B) := moduleTopology k (k ⊗[F] B)
  have : IsModuleTopology k (k ⊗[F] B) := ⟨rfl⟩
  have : IsTopologicalRing (k ⊗[F] B) := IsModuleTopology.isTopologicalRing k (k ⊗[F] B)
  have : IsModuleTopology k (Matrix (Fin 2) (Fin 2) (k ⊗[F] B)) :=
    (inferInstance : IsModuleTopology k (Fin 2 → Fin 2 → k ⊗[F] B))
  let bA := Module.finBasis k (Matrix (Fin 2) (Fin 2) (k ⊗[F] B))
  obtain ⟨U, hUo, hU1, hsq⟩ := exists_isOpen_mul_self_eq bA h2
  have he : Continuous bA.equivFun :=
    IsModuleTopology.continuous_of_linearMap bA.equivFun.toLinearMap
  have hτc : Continuous (τ.baseChange k) :=
    IsModuleTopology.continuous_of_linearMap (τ.baseChange k).toLinearMap
  have hmat : Continuous fun Z : Matrix (Fin 2) (Fin 2) (k ⊗[F] B) =>
      (τ.baseChange k).matrix (Fin 2) Z :=
    continuous_matrix fun i j => hτc.comp ((continuous_id.matrix_elem j i))
  have hΦ : Continuous fun g : Fin L → (k ⊗[F] B) × (k ⊗[F] B) => targetMap F B τ D g :=
    ((continuous_listProd_ofFn L).mul continuous_const).mul (hmat.comp (continuous_listProd_ofFn L))
  have hP : Continuous fun c : Fin L × Fin 2 × ι → k => coordPoint F B β c := by
    refine continuous_pi fun j => ?_
    refine Continuous.prodMk ?_ ?_
    · exact continuous_finsetSum _ fun i _ =>
        Continuous.smul (f := fun c : Fin L × Fin 2 × ι → k => c (j, 0, i))
          (g := fun _ => (1 : k) ⊗ₜ[F] β i) (continuous_apply _) continuous_const
    · exact continuous_finsetSum _ fun i _ =>
        Continuous.smul (f := fun c : Fin L × Fin 2 × ι → k => c (j, 1, i))
          (g := fun _ => (1 : k) ⊗ₜ[F] β i) (continuous_apply _) continuous_const
  have hV : (fun c => targetMap F B τ D (coordPoint F B β c)) ⁻¹' (bA.equivFun ⁻¹' U) ∈
      𝓝 (coordOf F B β g₀) := by
    refine ((hUo.preimage he).preimage (hΦ.comp hP)).mem_nhds ?_
    simp only [Set.mem_preimage, Function.comp_apply, coordPoint_coordOf, hg₀]
    exact hU1
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, t, ht, hIt⟩ := hV
  exact ⟨t, ht, fun c hc => hsq _ (hIt fun α _ => hc α)⟩

end Langlands.CentralSimple.Landherr
