/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Limits

/-! # FiniteAffineNormalizationCoproduct

## References

* Stacks Project and Mathlib
* Stacks Project, Tag 035I
-/

@[expose] public section

universe u
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private noncomputable def finCoproductIso {r : ℕ} (Z : Fin (r + 1) → Scheme.{u}) :
    (∐ Z) ≅ Z 0 ⨿ ∐ (fun i : Fin r ↦ Z i.succ) where
  hom := Sigma.desc (Fin.cases coprod.inl
    (fun i ↦ Sigma.ι (fun j : Fin r ↦ Z j.succ) i ≫ coprod.inr))
  inv := coprod.desc (Sigma.ι Z 0) (Sigma.desc (fun i : Fin r ↦ Sigma.ι Z i.succ))
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp
  inv_hom_id := by
    apply coprod.hom_ext
    · simp
    · apply Sigma.hom_ext
      intro i
      simp

set_option backward.isDefEq.respectTransparency false in
private theorem integral_fin_sigma_desc (r : ℕ) (Z : Fin r → Scheme.{u})
    (Y : Scheme.{u}) (g : ∀ i, Z i ⟶ Y) (hg : ∀ i, IsIntegralHom (g i)) :
    IsIntegralHom (Sigma.desc g) := by
  induction r with
  | zero =>
    let : IsEmpty (∐ Z : Scheme.{u}) := ⟨fun x ↦ by
      obtain ⟨i, _, _⟩ := (sigmaOpenCover Z).exists_eq x
      exact Fin.elim0 i⟩
    infer_instance
  | succ r ih =>
    let t := finCoproductIso Z
    let : IsIntegralHom (g 0) := hg 0
    let : IsIntegralHom (Sigma.desc (fun i : Fin r ↦ g i.succ)) :=
      ih (fun i ↦ Z i.succ) (fun i ↦ g i.succ) (fun i ↦ hg i.succ)
    have ht : Sigma.desc g = t.hom ≫
        coprod.desc (g 0) (Sigma.desc (fun i : Fin r ↦ g i.succ)) := by
      apply Sigma.hom_ext
      intro i
      refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp [t, finCoproductIso]
    rw [ht]
    infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Relative normalization of a finite affine coproduct. -/
theorem finite_affine_normalization_coproduct
    (A : CommRingCat.{u}) (r : ℕ) (D : Fin r → Type u)
    [∀ i, CommRing (D i)] [∀ i, Algebra A (D i)]
    (X : Scheme.{u}) (f : X ⟶ Spec A) [QuasiCompact f] [QuasiSeparated f]
    (e : X ≅ ∐ fun i : Fin r ↦ Spec (CommRingCat.of (D i)))
    (he : e.hom ≫ Sigma.desc (fun i : Fin r ↦
      Spec.map (CommRingCat.ofHom (algebraMap A (D i)))) = f) :
    ∃ n : (∐ fun i : Fin r ↦
        (Spec.map (CommRingCat.ofHom (algebraMap A (D i)))).normalization) ≅
        f.normalization,
      ∀ i : Fin r,
        Sigma.ι _ i ≫ n.hom ≫ f.fromNormalization =
          (Spec.map (CommRingCat.ofHom (algebraMap A (D i)))).fromNormalization  := by
  let g (i : Fin r) := Spec.map (CommRingCat.ofHom (algebraMap A (D i)))
  let N (i : Fin r) := (g i).normalization
  let j (i : Fin r) : Spec (CommRingCat.of (D i)) ⟶ X :=
    Sigma.ι (fun i : Fin r ↦ Spec (CommRingCat.of (D i))) i ≫ e.inv
  have hj (i : Fin r) : j i ≫ f = g i := by
    dsimp [j, g]
    rw [← he]
    simp
  let a (i : Fin r) : N i ⟶ f.normalization :=
    (g i).normalizationDesc (j i ≫ f.toNormalization) f.fromNormalization
      (by rw [Category.assoc, Hom.toNormalization_fromNormalization, hj])
  let b : (∐ N) ⟶ Spec A := Sigma.desc (fun i ↦ (g i).fromNormalization)
  let : IsIntegralHom b := integral_fin_sigma_desc r N (Spec A) _ (fun _ ↦ inferInstance)
  let v : X ⟶ ∐ N := e.hom ≫ CategoryTheory.Limits.Sigma.map
    (fun i : Fin r ↦ (g i).toNormalization)
  have hv : f = v ≫ b := by
    rw [← he]
    dsimp only [v, b]
    rw [Category.assoc]
    congr 1
    apply Sigma.hom_ext
    intro i
    simp [g]
  let z : f.normalization ⟶ ∐ N := f.normalizationDesc v b hv
  have hab : Sigma.desc a ≫ f.fromNormalization = b := by
    apply Sigma.hom_ext
    intro i
    simp [a, b]
  have hva : v ≫ Sigma.desc a = f.toNormalization := by
    rw [← cancel_epi e.inv]
    dsimp [v]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    apply Sigma.hom_ext
    intro i
    simp [a, j]
  have hza : z ≫ Sigma.desc a = 𝟙 _ := by
    apply Hom.normalization.hom_ext f _ _ f.fromNormalization
    · simp [z, hva]
    · rw [Category.assoc, hab]
      exact f.normalizationDesc_comp v b hv
    · simp
  have haz : Sigma.desc a ≫ z = 𝟙 _ := by
    apply Sigma.hom_ext
    intro i
    apply Hom.normalization.hom_ext (g i) _ _ b
    · simp [a, z, v, j]
    · simp only [Sigma.ι_comp_desc_assoc, Category.assoc]
      rw [show z ≫ b = f.fromNormalization from f.normalizationDesc_comp v b hv]
      exact (g i).normalizationDesc_comp _ _ _
    · simp [b]
  refine ⟨⟨Sigma.desc a, z, haz, hza⟩, ?_⟩
  intro i
  simp [a, g]

end AlgebraicGeometry.Scheme
