import Langlands.Algebra.CentralSimple.LandherrContinuity
import Langlands.Algebra.CentralSimple.LandherrStrongApprox
import Langlands.Algebra.CentralSimple.LandherrMainLemmas

/-! # Assembly lemmas: padded targets, scalar extension of products, coordinate approximation -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.Quaternionic Langlands.BinaryElementary Filter _root_.Topology
open NumberField IsDedekindDomain
open scoped TensorProduct

universe u

section Padding

variable {k : Type u} [NontriviallyNormedField k] [CompleteSpace k]
  (F : Type u) [Field F] [Algebra F k] (B : Type u) [Ring B] [Algebra F B] [FiniteDimensional F B]
  (τ : FirstKindInvolution F B) {ι : Type*} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F B)

/-- Let `B` be finite-dimensional over `F` and let `k` be a complete nontrivially normed
field over `F` with `2 ≠ 0`. If a list of entries gives the target `1`, then for every
length at least that of the list there are coordinate neighbourhoods on which the target
is a square in the `k`-subalgebra it generates. -/
theorem exists_target_nbhd (h2 : (2 : k) ≠ 0) (D : Matrix (Fin 2) (Fin 2) (k ⊗[F] B))
    (l : List ((k ⊗[F] B) × (k ⊗[F] B)))
    (hl : (listProd l : Matrix (Fin 2) (Fin 2) (k ⊗[F] B)) * D *
      (τ.baseChange k).matrix (Fin 2) (listProd l : Matrix (Fin 2) (Fin 2) (k ⊗[F] B)) = 1)
    (L : ℕ) (hL : l.length ≤ L) :
    ∃ c₀ : Fin L × Fin 2 × ι → k, ∃ t : Fin L × Fin 2 × ι → Set k, (∀ α, t α ∈ 𝓝 (c₀ α)) ∧
      ∀ c : Fin L × Fin 2 × ι → k, (∀ α, c α ∈ t α) →
        ∃ σ ∈ Algebra.adjoin k {targetMap F B τ D (coordPoint F B β c)},
          σ * σ = targetMap F B τ D (coordPoint F B β c) := by
  set padded := l ++ List.replicate (L - l.length) ((0 : k ⊗[F] B), (0 : k ⊗[F] B))
  have hlen : padded.length = L := by simp [padded]; omega
  let g₀ : Fin L → (k ⊗[F] B) × (k ⊗[F] B) := fun j => padded.getD j (0, 0)
  have hg₀ : List.ofFn g₀ = padded := ofFn_getD_eq padded (0, 0) L hlen
  have htarget : targetMap F B τ D g₀ = 1 := by
    rw [targetMap, hg₀, listProd_pad]
    exact hl
  obtain ⟨t, ht, hsq⟩ := exists_coord_nbhd F B τ β h2 D g₀ htarget
  exact ⟨coordOf F B β g₀, t, ht, hsq⟩

end Padding

section Extension

variable (F : Type u) [Field F] (B : Type u) [Ring B] [Algebra F B] [FiniteDimensional F B]
  (τ : FirstKindInvolution F B) (k : Type u) [Field k] [Algebra F k]

/-- Scalar extension commutes with the transposed involution on matrices. -/
theorem matrixBaseMap_matrix (Z : Matrix (Fin 2) (Fin 2) B) :
    matrixBaseMap F B k (τ.matrix (Fin 2) Z) = (τ.baseChange k).matrix (Fin 2) (matrixBaseMap F B k Z) := by
  ext i j
  simp [FirstKindInvolution.matrix_apply]

/-- Scalar extension of `t D τ(t)ᵗ` for an elementary product `t`. -/
theorem matrixBaseMap_targetMap (D : Matrix (Fin 2) (Fin 2) B) {L : ℕ} (g : Fin L → B × B) :
    matrixBaseMap F B k ((listProd (List.ofFn g) : Matrix (Fin 2) (Fin 2) B) * D *
        τ.matrix (Fin 2) (listProd (List.ofFn g) : Matrix (Fin 2) (Fin 2) B)) =
      targetMap F B τ (matrixBaseMap F B k D)
        (fun j => ((1 : k) ⊗ₜ[F] (g j).1, (1 : k) ⊗ₜ[F] (g j).2)) := by
  have hl : matrixBaseMap F B k (listProd (List.ofFn g) : Matrix (Fin 2) (Fin 2) B) =
      (listProd (List.ofFn fun j => ((1 : k) ⊗ₜ[F] (g j).1, (1 : k) ⊗ₜ[F] (g j).2)) :
        Matrix (Fin 2) (Fin 2) (k ⊗[F] B)) := by
    rw [matrixBaseMap_apply]
    have := map_listProd (Algebra.TensorProduct.includeRight : B →ₐ[F] k ⊗[F] B).toRingHom
      (List.ofFn g)
    rw [List.map_ofFn] at this
    exact this
  rw [map_mul, map_mul, matrixBaseMap_matrix, hl, targetMap]

end Extension

section Approximation

variable {F : Type u} [Field F] [NumberField F]

/-- **Coordinatewise strong approximation.** -/
theorem exists_approx_coords {κ : Type*} [Finite κ] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v₀ : HeightOneSpectrum (𝓞 F)) (hv₀ : v₀ ∉ S)
    (cf : ∀ v : HeightOneSpectrum (𝓞 F), κ → v.adicCompletion F)
    (Tf : ∀ v : HeightOneSpectrum (𝓞 F), κ → Set (v.adicCompletion F))
    (hTf : ∀ v ∈ S, ∀ α, Tf v α ∈ 𝓝 (cf v α))
    (ci : ∀ w : NumberField.InfinitePlace F, κ → w.Completion)
    (Ti : ∀ w : NumberField.InfinitePlace F, κ → Set w.Completion)
    (hTi : ∀ w α, Ti w α ∈ 𝓝 (ci w α)) :
    ∃ x : κ → F, (∀ v ∈ S, ∀ α, algebraMap F (v.adicCompletion F) (x α) ∈ Tf v α) ∧
      (∀ w α, algebraMap F w.Completion (x α) ∈ Ti w α) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v ≠ v₀ → ∀ α, v.valuation F (x α) ≤ 1 := by
  have h := fun α => exists_strongApprox S v₀ hv₀ (fun v => cf v α) (fun v => Tf v α)
    (fun v hv => hTf v hv α) (fun w => ci w α) (fun w => Ti w α) (fun w => hTi w α)
  choose x hxf hxi hxv using h
  exact ⟨x, fun v hv α => hxf α v hv, fun w α => hxi α w, fun v hv hv' α => hxv α v hv hv'⟩

end Approximation

end Langlands.CentralSimple.Landherr
