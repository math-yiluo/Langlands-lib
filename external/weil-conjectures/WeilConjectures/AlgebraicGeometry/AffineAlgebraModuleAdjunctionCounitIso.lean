/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorExtensionEpi
import Mathlib.CategoryTheory.Adjunction.Unique
/-! # Canonical affine algebra module adjunction component

Source: Stacks Project, Tags 0AVW and 01SB. -/

@[expose] public section

noncomputable section
universe v
open CategoryTheory
namespace AlgebraicGeometry

private theorem adjunction_of_epi_comparison
    {C A D : Type*} [Category C] [Category A] [Category D]
    (S : C ⥤ A) [S.Faithful] (T : A ⥤ D) (R : D ⥤ C) (H : C ⥤ D)
    (adj : T ⊣ R ⋙ S) (γ : S ⋙ T ⟶ H)
    (α : R ⋙ H ⟶ 𝟭 D) (β : 𝟭 C ⟶ H ⋙ R)
    (hα : ∀ F, γ.app (R.obj F) ≫ α.app F = adj.counit.app F)
    (hβ : ∀ G, S.map (β.app G) = adj.homEquiv _ _ (γ.app G))
    (hγ : ∀ G, Epi (γ.app G)) :
    Nonempty {a : H ⊣ R // a.counit = α} := by
  refine ⟨⟨{
    unit := β
    counit := α
    left_triangle_components := ?_
    right_triangle_components := ?_ }, rfl⟩⟩
  · intro G
    have := hγ G
    apply (cancel_epi (γ.app G)).mp
    have hn : T.map (S.map (β.app G)) ≫ γ.app (R.obj (H.obj G)) =
        γ.app G ≫ H.map (β.app G) := γ.naturality (β.app G)
    rw [← Category.assoc, ← hn, Category.assoc, hα]
    change T.map (S.map (β.app G)) ≫ adj.counit.app (H.obj G) = _
    rw [hβ]
    simpa only [Adjunction.homEquiv_counit, Category.comp_id] using
      (adj.homEquiv _ _).symm_apply_apply (γ.app G)
  · intro F
    apply S.map_injective
    rw [CategoryTheory.Functor.map_comp, hβ, S.map_id]
    change adj.homEquiv _ _ (γ.app (R.obj F)) ≫
      (R ⋙ S).map (α.app F) = 𝟙 _
    rw [← Adjunction.homEquiv_naturality_right, hα,
      ← adj.homEquiv_symm_id F]
    exact Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical affine algebra adjunction component.
Source: Stacks Project, Tags 0AVW and 01SB.
(blueprint: new-affine-algebra-module-counit-iso).

Proof: Identify the canonical left adjoint with tensor pullback for g by its Hom adjunction. Tensor
associativity identifies it with the two operations in the affine module correspondence. Its
counit is alpha: on pure tensors the evaluation sends a tensor s to a times s, uniquely by the
tensor universal property. The correspondence proves alpha invertible on quasi-coherent O_X-
modules. Transport it across the adjunction-compatible isomorphism of left adjoints. No
surjectivity of f is used; empty schemes and zero modules satisfy the claim.
-/
theorem affine_algebra_module_adjunction_counit_iso
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [(RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).IsRightAdjoint] :
    ∀ K : SheafOfModules.{v} (moduleRings X.toRingedSpace),
      K.IsQuasicoherent → IsIso
        ((Adjunction.ofIsRightAdjoint
          (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))).counit.app K) := by
  classical
  intro K hK
  have hc := Scheme.Modules.affine_module_correspondence f
  refine Exists.elim hc.2.2 (fun B hB ↦ ?_)
  refine Exists.elim hB (fun b hb ↦ ?_)
  refine Exists.elim hb (fun t ht ↦ ?_)
  refine Exists.elim ht (fun ε hring ↦ ?_)
  refine Exists.elim hring.2.2.2 (fun P hP₀ ↦ ?_)
  refine Exists.elim hP₀ (fun pobj hP₁ ↦ ?_)
  refine Exists.elim hP₁ (fun κ hP ↦ ?_)
  refine Exists.elim hP.2.2 (fun H hH₀ ↦ ?_)
  refine Exists.elim hH₀ (fun hobj hH₁ ↦ ?_)
  refine Exists.elim hH₁ (fun γ hH ↦ ?_)
  refine Exists.elim hH.2.2.2 (fun α hβ₀ ↦ ?_)
  refine Exists.elim hβ₀ (fun β hcomp ↦ ?_)
  let A := (TopCat.Sheaf.pushforward CommRingCat.{v} f.base).obj X.sheaf
  let ρ : Y.sheaf ⟶ A := ⟨f.c⟩
  let S := SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{v} RingCat.{v})).map ρ)
  have : S.Faithful := ⟨fun {_ _} _ _ h ↦ by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext m
    exact congrArg (fun q ↦ q.val.app V m) h⟩
  have hγ := Scheme.Modules.affine_module_tensor_extension_epi f B b ε P κ
    H hobj γ hH.2.1
  let R := SheafOfModules.pushforward.{v} (F := TopologicalSpace.Opens.map f.base)
    (S := (sheafCompose _ (forget₂ CommRingCat.{v} RingCat.{v})).obj A)
    (R := X.ringCatSheaf)
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{v} RingCat.{v})).obj A))
  let adj₀ := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)
  obtain ⟨a, ha⟩ := adjunction_of_epi_comparison S (Scheme.Modules.tensorPullback f)
    R H adj₀
    γ α β hcomp.1 hcomp.2.1 hγ
  let G := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let adj := Adjunction.ofIsRightAdjoint G
  have : IsIso (a.counit.app K) := by
    rw [ha]
    exact hcomp.2.2.1 K hK
  rw [← adj.leftAdjointUniq_hom_app_counit a K]
  infer_instance
end AlgebraicGeometry
