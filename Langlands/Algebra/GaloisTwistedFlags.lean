import Langlands.Algebra.GaloisTwistedSubspaces
import Langlands.Algebra.GaloisTwistedCompression
import Langlands.GroupScheme.MatrixRepresentation.NormalFixedRepresentation
import Langlands.GroupScheme.MatrixRepresentation.MinimalStableSubrepresentation

/-! # Rational idempotents adapted to a twisted-stable flag -/

noncomputable section

universe u

open scoped Matrix

namespace Langlands.Algebra.GaloisTwistedMatrix

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Twisted stability of a subspace: `u ∈ V ⇒ σ⁻¹(P σ u) ∈ V` for every `σ`. -/
def IsTwistedStable (P : (K ≃ₐ[k] K) → Matrix n n K) (V : Submodule K (n → K)) : Prop :=
  ∀ σ : K ≃ₐ[k] K, ∀ u ∈ V, (fun i => σ.symm ((P σ *ᵥ u) i)) ∈ V

omit [IsGalois k K] [DecidableEq n] in
theorem symm_map_mulVec {m : Type} [Fintype m] (σ : K ≃ₐ[k] K) (F : Matrix m n K) (v : n → K) :
    (fun i => σ.symm ((F.map σ *ᵥ v) i)) = F *ᵥ (fun j => σ.symm (v j)) := by
  funext i
  have h := RingHom.map_mulVec (σ.symm : K →+* K) (F.map σ) v i
  simpa [Function.comp_def, Matrix.map_map] using h

/-- For a twisted-stable flag `Y ≤ X`, the descended algebra contains an idempotent with image
in `X`, killing `Y`, and congruent to the identity modulo `Y` on `X`. -/
theorem exists_adapted_idempotent [Nonempty n] (P : (K ≃ₐ[k] K) → Matrix n n K)
    (hP : ∀ σ, IsUnit (P σ)) (A : Subalgebra k (Matrix n n K)) (hA : A ≤ twistedFixed P)
    (hspan : Submodule.span K (A : Set (Matrix n n K)) = ⊤) {X Y : Submodule K (n → K)}
    (hYX : Y ≤ X) (hX : IsTwistedStable P X) (hY : IsTwistedStable P Y) :
    ∃ f ∈ A, f * f = f ∧ (∀ v, f *ᵥ v ∈ X) ∧ (∀ y ∈ Y, f *ᵥ y = 0) ∧
      (∀ x ∈ X, f *ᵥ x - x ∈ Y) := by
  classical
  -- an idempotent `g ∈ A` with image `X`
  obtain ⟨e₁, he₁A, he₁, he₁ker⟩ := exists_idempotent_ker_eq P hP A hA hspan X hX
  set g := 1 - e₁ with hg
  have hgA : g ∈ A := A.sub_mem A.one_mem he₁A
  have hgX : ∀ v, g *ᵥ v ∈ X := fun v => by
    rw [← he₁ker, hg, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec, he₁, sub_self]
  have hgid : ∀ x ∈ X, g *ᵥ x = x := fun x hx => by
    rw [hg, Matrix.sub_mulVec, Matrix.one_mulVec, (he₁ker x).mpr hx, sub_zero]
  -- coordinates of `X`
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ :=
    GroupScheme.MatrixRepresentation.exists_subspace_split_coordinates X
  have hBX : ∀ w, B *ᵥ w ∈ X := fun w => by
    rw [← GroupScheme.MatrixRepresentation.range_coordinateInclusion_eq X B C hcols hproj]
    exact ⟨w, rfl⟩
  have hgB : g * B = B := by
    ext i j
    have := congrFun (hgid _ (hcols j)) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  set Fx := C * g with hFx
  have hFE : Fx * B = 1 := by rw [hFx, Matrix.mul_assoc, hgB, hCB]
  have hEF : B * Fx = g := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_apply, hFx, ← Matrix.mulVec_mulVec]
    rw [Matrix.mulVec_mulVec (M := B) (N := C), hproj _ (hgX v)]
  have hEFA : B * Fx ∈ A := by rw [hEF]; exact hgA
  by_cases hd : d = 0
  · subst hd
    refine ⟨0, A.zero_mem, by simp, fun v => by simp, fun y _ => by simp, fun x hx => ?_⟩
    have hx0 : x = 0 := by
      rw [← hproj x hx]
      funext i
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [hx0]
    simp
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
  -- the corner of `A` on `X`, in coordinates
  set S := compressed A Fx B hFE hEFA with hS
  have hSle := compressed_le_twistedFixed hA Fx B hFE hEFA
  have hSu := isUnit_compressed_twist hA hP Fx B hFE hEFA
  have hSspan := span_compressed hspan Fx B hFE hEFA
  set Y' := Y.comap B.mulVecLin with hY'
  have hY'st : IsTwistedStable (fun σ => Fx.map σ * P σ * B) Y' := by
    intro σ u hu
    have hBu : B *ᵥ u ∈ Y := hu
    change B *ᵥ (fun i => σ.symm (((Fx.map σ * P σ * B) *ᵥ u) i)) ∈ Y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, symm_map_mulVec, Matrix.mulVec_mulVec,
      hEF]
    rw [hgid _ (hYX (hY σ _ hBu))]
    exact hY σ _ hBu
  obtain ⟨e', he'S, he', he'ker⟩ := exists_idempotent_ker_eq _ hSu S hSle hSspan Y' hY'st
  obtain ⟨a, haA, rfl⟩ := he'S
  -- the adapted idempotent
  refine ⟨B * (Fx * a * B) * Fx, ?_, ?_, ?_, ?_, ?_⟩
  · have : B * (Fx * a * B) * Fx = g * a * g := by
      simp only [← hEF, Matrix.mul_assoc]
    rw [this]
    exact A.mul_mem (A.mul_mem hgA haA) hgA
  · calc B * (Fx * a * B) * Fx * (B * (Fx * a * B) * Fx)
        = B * ((Fx * a * B) * (Fx * B) * (Fx * a * B)) * Fx := by
          simp only [Matrix.mul_assoc]
      _ = B * (Fx * a * B) * Fx := by rw [hFE, Matrix.mul_one, he']
  · intro v
    simp only [← Matrix.mulVec_mulVec]
    exact hBX _
  · intro y hy
    have hyX := hYX hy
    have hFy : Fx *ᵥ y ∈ Y' := by
      change B *ᵥ (Fx *ᵥ y) ∈ Y
      rw [Matrix.mulVec_mulVec, hEF, hgid y hyX]
      exact hy
    have h0 := (he'ker _).mpr hFy
    simp only [← Matrix.mulVec_mulVec] at h0 ⊢
    rw [h0, Matrix.mulVec_zero]
  · intro x hx
    have hxB : x = B *ᵥ (Fx *ᵥ x) := by rw [Matrix.mulVec_mulVec, hEF, hgid x hx]
    set u := Fx *ᵥ x
    have hdiff : (Fx * a * B) *ᵥ u - u ∈ Y' := by
      rw [← he'ker, Matrix.mulVec_sub, Matrix.mulVec_mulVec, he', sub_self]
    have : (B * (Fx * a * B) * Fx) *ᵥ x - x = B *ᵥ ((Fx * a * B) *ᵥ u - u) := by
      conv_lhs => rw [hxB]
      rw [Matrix.mulVec_sub]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hFE, Matrix.mul_one]
    rw [this]
    exact hdiff

end Langlands.Algebra.GaloisTwistedMatrix
