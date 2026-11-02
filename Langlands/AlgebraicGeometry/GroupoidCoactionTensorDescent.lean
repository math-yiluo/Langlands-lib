import Langlands.AlgebraicGeometry.GroupoidCoactionTensorPresentation
import Langlands.AlgebraicGeometry.FlatTensorCoactionZeroDetection

/-! # Flat descent in tensor-presentation coordinates -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable {M : Type v} [AddCommGroup M] [Module B M] [Module A M]
  [IsScalarTower A B M]
variable {t : B →+* C}

/-- Three tensor coordinates, with the module attached to the first factor. -/
noncomputable def presentationTripleEquiv :
    (B ⊗[A] (B ⊗[A] B)) ⊗[B] M ≃ₗ[A] B ⊗[A] (B ⊗[A] M) :=
  ((TensorProduct.comm B (B ⊗[A] (B ⊗[A] B)) M).restrictScalars A).trans
    (((AlgebraTensorModule.cancelBaseChange A B B M (B ⊗[A] B)).restrictScalars A).trans
      ((TensorProduct.comm A M (B ⊗[A] B)).trans
        ((TensorProduct.congr (TensorProduct.comm A B B) (LinearEquiv.refl A M)).trans
          (TensorProduct.assoc A B B M))))

@[simp]
lemma presentationTripleEquiv_tmul (b₃ b₂ b₁ : B) (m : M) :
    presentationTripleEquiv (A := A) ((b₃ ⊗ₜ[A] (b₂ ⊗ₜ[A] b₁)) ⊗ₜ[B] m) =
      b₁ ⊗ₜ[A] (b₂ ⊗ₜ[A] (b₃ • m)) := by
  simp [presentationTripleEquiv]

@[simp]
lemma presentationTensorEquiv_symm_tmul (e : C ≃ₐ[B] B ⊗[A] B)
    (ht : ∀ b : B, e (t b) = (1 : B) ⊗ₜ[A] b) (b : B) (m : M) :
    (presentationTensorEquiv e).symm (b ⊗ₜ[A] m) = t b ⊗ₜ[B] m := by
  apply (presentationTensorEquiv e).injective
  rw [LinearEquiv.apply_symm_apply]
  have hb : t b = e.symm ((1 : B) ⊗ₜ[A] b) := by
    apply e.injective
    simp [ht]
  rw [hb, presentationTensorEquiv_tmul, one_smul]

/-- The point with source in the middle factor and target in the last. -/
noncomputable def presentationFirst (e : C ≃ₐ[B] B ⊗[A] B) :
    C →+* B ⊗[A] (B ⊗[A] B) :=
  ((Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).comp
    (e.restrictScalars A).toAlgHom).toRingHom

/-- The point with source in the first factor and target in the middle. -/
noncomputable def presentationSecond (e : C ≃ₐ[B] B ⊗[A] B) :
    C →ₐ[B] B ⊗[A] (B ⊗[A] B) :=
  (Algebra.TensorProduct.map (AlgHom.id B B)
    (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).comp e.toAlgHom

/-- The point with source in the first factor and target in the last. -/
noncomputable def presentationComposite (e : C ≃ₐ[B] B ⊗[A] B) :
    C →ₐ[B] B ⊗[A] (B ⊗[A] B) :=
  (Algebra.TensorProduct.map (AlgHom.id B B)
    (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).comp e.toAlgHom

lemma presentation_points_compat (e : C ≃ₐ[B] B ⊗[A] B)
    (ht : ∀ b : B, e (t b) = (1 : B) ⊗ₜ[A] b) :
    (presentationFirst e).comp (algebraMap B C) =
      (presentationSecond e : C →+* B ⊗[A] (B ⊗[A] B)).comp t := by
  ext b
  simp [presentationFirst, presentationSecond, ht]

lemma presentation_composite_target (e : C ≃ₐ[B] B ⊗[A] B)
    (ht : ∀ b : B, e (t b) = (1 : B) ⊗ₜ[A] b) :
    (presentationComposite e : C →+* B ⊗[A] (B ⊗[A] B)).comp t =
      (presentationFirst e).comp t := by
  ext b
  simp [presentationFirst, presentationComposite, ht]

lemma presentationTripleEquiv_composite (e : C ≃ₐ[B] B ⊗[A] B)
    (ht : ∀ b : B, e (t b) = (1 : B) ⊗ₜ[A] b) (x : C ⊗[B] M) :
    presentationTripleEquiv
      (LinearMap.rTensor M (presentationComposite e).toLinearMap x) =
        LinearMap.lTensor B tensorCoactionUnit (presentationTensorEquiv e x) := by
  have aux (y : B ⊗[A] M) :
      presentationTripleEquiv
        (LinearMap.rTensor M (presentationComposite e).toLinearMap
          ((presentationTensorEquiv e).symm y)) =
        LinearMap.lTensor B tensorCoactionUnit y := by
    induction y with
    | tmul b m =>
      rw [presentationTensorEquiv_symm_tmul e ht]
      simp [presentationComposite, ht]
    | add y z hy hz => simp [hy, hz]
  simpa using aux (presentationTensorEquiv e x)

lemma presentationTripleEquiv_first_second (e : C ≃ₐ[B] B ⊗[A] B)
    (ht : ∀ b : B, e (t b) = (1 : B) ⊗ₜ[A] b) (b : B) (x : C ⊗[B] M) :
    presentationTripleEquiv
      (presentationFirst e (t b) •
        LinearMap.rTensor M (presentationSecond e).toLinearMap x) =
      b ⊗ₜ[A] presentationTensorEquiv e x := by
  have aux (y : B ⊗[A] M) :
      presentationTripleEquiv
        (presentationFirst e (t b) •
          LinearMap.rTensor M (presentationSecond e).toLinearMap
            ((presentationTensorEquiv e).symm y)) =
        b ⊗ₜ[A] y := by
    induction y with
    | tmul d m =>
      rw [presentationTensorEquiv_symm_tmul e ht]
      simp [presentationFirst, presentationSecond, ht, smul_tmul', smul_eq_mul]
    | add y z hy hz => simp [smul_add, tmul_add, hy, hz]
  simpa using aux (presentationTensorEquiv e x)

lemma presentationTripleEquiv_coactionCompose (θ : GroupoidCoaction t M)
    (e : C ≃ₐ[B] B ⊗[A] B)
    (ht : ∀ b : B, e (t b) = (1 : B) ⊗ₜ[A] b) (x : C ⊗[B] M) :
    presentationTripleEquiv
      (coactionCompose t M θ.coaction θ.map_smul
        (presentationFirst e) (presentationSecond e) (presentation_points_compat e ht) x) =
      LinearMap.lTensor B (presentationCoaction θ e ht) (presentationTensorEquiv e x) := by
  have aux (y : B ⊗[A] M) :
      presentationTripleEquiv
        (coactionCompose t M θ.coaction θ.map_smul
          (presentationFirst e) (presentationSecond e) (presentation_points_compat e ht)
          ((presentationTensorEquiv e).symm y)) =
        LinearMap.lTensor B (presentationCoaction θ e ht) y := by
    induction y with
    | tmul b m =>
      rw [presentationTensorEquiv_symm_tmul e ht]
      change presentationTripleEquiv
        (presentationFirst e (t b) •
          LinearMap.rTensor M (presentationSecond e).toLinearMap (θ.coaction m)) =
          b ⊗ₜ[A] presentationCoaction θ e ht m
      exact presentationTripleEquiv_first_second e ht b (θ.coaction m)
    | add y z hy hz => simp [hy, hz]
  simpa using aux (presentationTensorEquiv e x)

/-- The published cocycle gives the ordinary iterated-tensor coaction identity. -/
lemma presentationCoaction_coassoc (θ : GroupoidCoaction t M)
    (e : C ≃ₐ[B] B ⊗[A] B)
    (ht : ∀ b : B, e (t b) = (1 : B) ⊗ₜ[A] b) (m : M) :
    LinearMap.lTensor B (presentationCoaction θ e ht) (presentationCoaction θ e ht m) =
      LinearMap.lTensor B tensorCoactionUnit (presentationCoaction θ e ht m) := by
  have h := congrArg (presentationTripleEquiv (A := A) (M := M))
    (θ.coassoc (B ⊗[A] (B ⊗[A] B)) (presentationFirst e)
      (presentationSecond e) (presentationComposite e)
      (presentation_points_compat e ht) (presentation_composite_target e ht) m)
  rw [presentationTripleEquiv_composite e ht, presentationTripleEquiv_coactionCompose θ e ht] at h
  exact h.symm

/-- Flatness over the presentation base detects a nonzero invariant element. -/
lemma exists_nonzero_invariant_of_flat_presentation [Module.Flat A B] [Nontrivial M]
    (hE : RingEtaleEquivalenceRelation t) (θ : GroupoidCoaction t M)
    (e : C ≃ₐ[B] B ⊗[A] B)
    (ht : ∀ b : B, e (t b) = (1 : B) ⊗ₜ[A] b) :
    ∃ m ∈ θ.invariants, m ≠ 0 := by
  obtain ⟨m, hm, hn⟩ := exists_nonzero_fixed_of_flat_tensor_coaction
    (presentationCoaction θ e ht) (presentationCoaction_injective hE θ e ht)
    (presentationCoaction_coassoc θ e ht)
  exact ⟨m, (presentationCoaction_fixed_iff θ e ht m).mp hm, hn⟩

end Langlands.AlgebraicGeometry.GroupoidCoaction
