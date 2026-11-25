/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits

/-! # FiniteAffineTensorBaseChange

## References

* Stacks Project and Mathlib
* Stacks Project, Tag 01JO
-/

@[expose] public section

universe u
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Finite affine coproducts commute with tensor base change. -/
theorem finite_affine_tensor_base_change
    (B A : CommRingCat.{u}) [Algebra B A]
    (r : ℕ) (E : Fin r → Type u) [∀ i, CommRing (E i)] [∀ i, Algebra B (E i)]
    (X : Scheme.{u}) (p : X ⟶ Spec B)
    (e : X ≅ ∐ fun i : Fin r ↦ Spec (CommRingCat.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i : Fin r ↦
      Spec.map (CommRingCat.ofHom (algebraMap B (E i)))) = p) :
    ∃ t : pullback p (Spec.map (CommRingCat.ofHom (algebraMap B A))) ≅
        ∐ fun i : Fin r ↦ Spec (CommRingCat.of (E i ⊗[B] A)),
      t.hom ≫ Sigma.desc (fun i : Fin r ↦ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[B] E i ⊗[B] A).toRingHom)) =
        pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap B A)))  := by
  classical
  let g := Spec.map (CommRingCat.ofHom (algebraMap B A))
  let Z (i : Fin r) := Spec (CommRingCat.of (E i))
  let T (i : Fin r) := Spec (CommRingCat.of (E i ⊗[B] A))
  let U := (sigmaOpenCover Z).pushforwardIso e.inv
  let V : (pullback p g).OpenCover := U.pullback₁ (pullback.fst p g)
  have hj (i : Fin r) : U.f i ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap B (E i))) := by
    dsimp [U]
    rw [← he]
    simp [Z]
  let q (i : Fin r) : V.X i ≅ T i :=
    pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso p g (U.f i) ≪≫
      pullback.congrHom (hj i) rfl ≪≫ pullbackSpecIso B (E i) A
  let k (i : Fin r) : T i ⟶ pullback p g := (q i).inv ≫ V.f i
  have hkfst (i : Fin r) : k i ≫ pullback.fst p g =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : E i →ₐ[B] E i ⊗[B] A).toRingHom) ≫
          U.f i := by
    change (q i).inv ≫ pullback.fst (pullback.fst p g) (U.f i) ≫
      pullback.fst p g = _
    simp [q, g, pullback.congrHom_inv]
    rfl
  have hksnd (i : Fin r) : k i ≫ pullback.snd p g =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[B] E i ⊗[B] A).toRingHom) := by
    change (q i).inv ≫ pullback.fst (pullback.fst p g) (U.f i) ≫
      pullback.snd p g = _
    simp [q, g, pullback.congrHom_inv]
  let (i : Fin r) : IsOpenImmersion (k i) := by
    dsimp [k]
    infer_instance
  have hkdisj : Pairwise (fun i j ↦ Disjoint (Set.range (k i)) (Set.range (k j))) := by
    intro i j hij
    apply Set.disjoint_iff_forall_ne.mpr
    rintro _ ⟨xi, rfl⟩ _ ⟨xj, rfl⟩ h
    have h' := congrArg (fun z ↦ e.hom (pullback.fst p g z)) h
    have hi := congrArg (fun f ↦ f xi) (hkfst i)
    have hj := congrArg (fun f ↦ f xj) (hkfst j)
    simp only [Hom.comp_apply] at hi hj
    rw [hi, hj] at h'
    simp only [U, Cover.pushforwardIso_f, sigmaOpenCover_f] at h'
    simp only [← Hom.comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id] at h'
    exact hij (congrArg Sigma.fst ((sigmaι_eq_iff Z i j _ _).mp h'))
  let : IsOpenImmersion (Sigma.desc k) := isOpenImmersion_sigmaDesc T k hkdisj
  have hsurj : Function.Surjective (Sigma.desc k) := by
    intro x
    obtain ⟨i, y, hy⟩ := V.exists_eq x
    refine ⟨Sigma.ι T i ((q i).hom y), ?_⟩
    rw [← Hom.comp_apply, Sigma.ι_comp_desc]
    change V.f i ((q i).inv ((q i).hom y)) = x
    have hyy : (q i).inv ((q i).hom y) = y := by
      rw [← Hom.comp_apply, (q i).hom_inv_id]
      rfl
    rw [hyy]
    exact hy
  let : Epi (Sigma.desc k).base := (TopCat.epi_iff_surjective _).mpr hsurj
  let : IsIso (Sigma.desc k) := IsOpenImmersion.isIso (Sigma.desc k)
  refine ⟨(asIso (Sigma.desc k)).symm, ?_⟩
  rw [← cancel_epi (Sigma.desc k)]
  simp only [Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc]
  apply Sigma.hom_ext
  intro i
  simpa only [T, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc] using (hksnd i).symm

end AlgebraicGeometry.Scheme
