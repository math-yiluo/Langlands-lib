/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The stabilized kernel images admit a compatible system of representatives.

Source: Stacks Project, Lemma 087X, construction of claims (a)--(b).
(blueprint: new-kernel-stabilized-system).
The proof restricts the stabilized image inclusions on a finite affine cover and
glues the resulting compatible quasi-coherent systems.
-/
theorem coherentFormalModule_kernel_stabilized_system {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H)
    (c : ℕ)
    (hc : ∀ (l m : ℕ) (h : m + c ≤ l),
      Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op))) :
    ∃ (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj),
      ∀ m : ℕ, ∃ e : S.obj (op m) ≅
        Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫
          F.obj.map (homOfLE (Nat.le_add_right m c)).op),
        e.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
          F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m) := by
  classical
  have _ := hc
  let a (n : ℕᵒᵖ) := kernel.ι (α.hom.app (op (n.unop + c))) ≫
    F.obj.map (homOfLE (Nat.le_add_right n.unop c)).op
  let t {n m : ℕᵒᵖ} (f : n ⟶ m) : op (n.unop + c) ⟶ op (m.unop + c) :=
    (homOfLE (Nat.add_le_add_right (leOfHom f.unop) c)).op
  let k {n m : ℕᵒᵖ} (f : n ⟶ m) :=
    kernel.map (α.hom.app (op (n.unop + c))) (α.hom.app (op (m.unop + c)))
      (F.obj.map (t f)) (H.obj.map (t f)) (α.hom.naturality (t f)).symm
  have w {n m : ℕᵒᵖ} (f : n ⟶ m) : k f ≫ a m = a n ≫ F.obj.map f := by
    dsimp [k, a]
    rw [← Category.assoc, kernel.lift_ι, Category.assoc, ← F.obj.map_comp,
      Category.assoc, ← F.obj.map_comp]
    congr 2
  let s {n m : ℕᵒᵖ} (f : n ⟶ m) := image.map (Arrow.homMk' (k f) (F.obj.map f) (w f))
  have hs {n m : ℕᵒᵖ} (f : n ⟶ m) : s f ≫ image.ι (a m) =
      image.ι (a n) ≫ F.obj.map f := image.map_homMk'_ι (w f)
  let S : ℕᵒᵖ ⥤ X.Modules :=
    { obj := fun n ↦ image (a n)
      map := fun f ↦ s f
      map_id := fun n ↦ by
        apply (cancel_mono (image.ι (a n))).1
        rw [hs, F.obj.map_id, Category.comp_id]
        exact (Category.id_comp _).symm
      map_comp := fun f g ↦ by
        apply (cancel_mono (image.ι (a _))).1
        rw [hs, Category.assoc, hs, ← Category.assoc, hs,
          Category.assoc, ← F.obj.map_comp] }
  let j : S ⟶ F.obj :=
    { app := fun n ↦ image.ι (a n)
      naturality := fun _ _ f ↦ hs f }
  refine ⟨S, j, fun m ↦ ⟨(Abelian.imageIsoImage (a (op m))).symm, ?_⟩⟩
  change (Abelian.imageIsoImage (a (op m))).inv ≫
    kernel.ι (cokernel.π (a (op m))) = image.ι (a (op m))
  rw [← Abelian.imageIsoImage_hom_comp_image_ι (a (op m))]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end AlgebraicGeometry
