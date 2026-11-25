/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal

/-! # ScalarPullbackTensorCoefficient

Source: Stacks Project, Cohomology, Tags 01F7, 01FD, 07MB and 0FKV.
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Sheaf.monoidalCategory HasExt.standard
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

@[reassoc]
private theorem scalar_pushforward_tensor (t : Y ⟶ X) (A B : KSheaf Y k) :
    Functor.LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology X)
      (ModuleCat.{w} k))
      (((Opens.map t.base).sheafPushforwardContinuous (ModuleCat.{w} k)
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj A)
      (((Opens.map t.base).sheafPushforwardContinuous (ModuleCat.{w} k)
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj B) ≫
      (Functor.LaxMonoidal.μ
        ((Opens.map t.base).sheafPushforwardContinuous (ModuleCat.{w} k)
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)) A B).hom =
    Functor.whiskerLeft (Opens.map t.base).op
      (Functor.LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology Y)
        (ModuleCat.{w} k)) A B) := by
  apply NatTrans.ext
  funext U
  exact Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (Opens.map t.base) (ModuleCat.{w} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) A B U

/-- Perform the monoidal adjunction calculation with abstract coefficient sheaves. -/
private theorem scalar_tensor_comparison_of_adjoints (t : Y ⟶ X)
    {A B H : KSheaf X k} {C D I J : KSheaf Y k}
    (a : A ⊗ B ⟶ H) (b : (scalarInverseImage t).obj H ⟶ I) (c : I ⟶ J)
    (jA : (scalarInverseImage t).obj A ⟶ C) (jB : (scalarInverseImage t).obj B ⟶ D)
    (d : C ⊗ D ⟶ J)
    (h : a ≫ ((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).homEquiv H I b ≫
        ((Opens.map t.base).sheafPushforwardContinuous (ModuleCat.{w} k)
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map c =
      (((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).homEquiv A C jA ⊗ₘ
        ((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).homEquiv B D jB) ≫
        Functor.LaxMonoidal.μ ((Opens.map t.base).sheafPushforwardContinuous (ModuleCat.{w} k)
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)) C D ≫
        ((Opens.map t.base).sheafPushforwardContinuous (ModuleCat.{w} k)
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map d) :
    (scalarInverseImage t).map a ≫ b ≫ c =
      ((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).leftAdjointOplaxMonoidal.δ
          A B ≫ (jA ⊗ₘ jB) ≫ d := by
  let adj := (Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  apply (adj.homEquiv _ _).injective
  dsimp only [scalarInverseImage]
  rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right,
    Adjunction.leftAdjointOplaxMonoidal_δ,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_assoc,
    tensorHom_comp_tensorHom_assoc]
  simpa only [← Adjunction.homEquiv_unit] using h

/-- Reduce the pushforward tensor comparison to pure tensors before specializing the sheaves. -/
private theorem scalar_tensor_comparison_of_sections (t : Y ⟶ X)
    {A B H : KSheaf X k} {C D I J : KSheaf Y k}
    (a : A ⊗ B ⟶ H)
    (b : H ⟶ ((Opens.map t.base).sheafPushforwardContinuous (ModuleCat.{w} k)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj I)
    (c : I ⟶ J)
    (jA : A ⟶ ((Opens.map t.base).sheafPushforwardContinuous (ModuleCat.{w} k)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj C)
    (jB : B ⟶ ((Opens.map t.base).sheafPushforwardContinuous (ModuleCat.{w} k)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj D)
    (d : C ⊗ D ⟶ J)
    (h : ∀ (U : (Opens X)ᵒᵖ) (s : A.obj.obj U) (r : B.obj.obj U),
      c.hom.app ((Opens.map t.base).op.obj U)
        (b.hom.app U (a.hom.app U
          ((Functor.LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology X)
            (ModuleCat.{w} k)) A B).app U (s ⊗ₜ[k] r)))) =
      d.hom.app ((Opens.map t.base).op.obj U)
        ((Functor.LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology Y)
          (ModuleCat.{w} k)) C D).app ((Opens.map t.base).op.obj U)
            (jA.hom.app U s ⊗ₜ[k] jB.hom.app U r))) :
    a ≫ b ≫ ((Opens.map t.base).sheafPushforwardContinuous (ModuleCat.{w} k)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map c =
    (jA ⊗ₘ jB) ≫
      Functor.LaxMonoidal.μ ((Opens.map t.base).sheafPushforwardContinuous (ModuleCat.{w} k)
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)) C D ≫
      ((Opens.map t.base).sheafPushforwardContinuous (ModuleCat.{w} k)
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map d := by
  apply Sheaf.hom_ext_of_μ_comp
  simp only [ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom]
  have hn {A B C D : KSheaf X k} (a : A ⟶ C) (b : B ⟶ D) :
      Functor.LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology X)
        (ModuleCat.{w} k)) A B ≫ (a ⊗ₘ b).hom =
      (a.hom ⊗ₘ b.hom) ≫
        Functor.LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology X)
          (ModuleCat.{w} k)) C D :=
    (Functor.LaxMonoidal.μ_natural
      (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{w} k)) a b).symm
  simp only [← Category.assoc]
  rw [hn]
  simp only [Category.assoc]
  rw [scalar_pushforward_tensor_assoc]
  apply NatTrans.ext
  funext U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s r
  simp only [NatTrans.comp_app, ModuleCat.comp_apply]
  erw [Monoidal.FunctorCategory.tensorHom_app, ModuleCat.MonoidalCategory.tensorHom_tmul]
  exact h U s r

/-- The scalar pullback adjunct evaluates to the normalized module pullback unit. -/
private theorem scalar_pullback_adjunct_app
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ X) (ht : t ≫ f = g) (H : X.Modules) (U : (Opens X)ᵒᵖ) (z : H.val.obj U) :
    ((((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).homEquiv _ _)
        (scalarPullbackCoefficient f g t ht H)).hom.app U z =
      ((Classical.choose (exists_tensorPullbackAdjunction t)).unit.app H).val.app U z := by
  unfold scalarPullbackCoefficient
  exact Classical.choose_spec (exists_scalarPullbackCoefficient f g t ht H) U.unop z

/-- The normalized tensor comparison agrees with the scalar tensor coefficient on unit sections. -/
private theorem scalar_tensor_pullback_unit
    (g : Y ⟶ Spec (CommRingCat.of k)) (t : Y ⟶ X) (F G : X.Modules)
    (U : (Opens X)ᵒᵖ) (s : F.val.obj U) (r : G.val.obj U) :
    (scalarHom g ((Classical.choose (module_pullback_tensor t)) F G).hom).hom.app
      (Opposite.op (t ⁻¹ᵁ U.unop))
      (((Classical.choose (exists_tensorPullbackAdjunction t)).unit.app (F ⊗ G)).val.app
        U (tmulSection s r)) =
    (scalarTensorCoefficient g ((tensorPullback t).obj F) ((tensorPullback t).obj G)).hom.app
      (Opposite.op (t ⁻¹ᵁ U.unop))
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology Y)
        (ModuleCat.{w} k)) (scalarSheaf g ((tensorPullback t).obj F))
          (scalarSheaf g ((tensorPullback t).obj G))).app (Opposite.op (t ⁻¹ᵁ U.unop))
        ((((Classical.choose (exists_tensorPullbackAdjunction t)).unit.app F).val.app U s)
          ⊗ₜ[k] (((Classical.choose (exists_tensorPullbackAdjunction t)).unit.app G).val.app
            U r))) := by
  erw [exists_scalarTensorCoefficient]
  exact (Classical.choose_spec (module_pullback_tensor t)).2 F G U.unop s r

/-- The scalar tensor coefficient commutes with the normalized module pullback
comparison. This is an equality of coefficient sheaf morphisms, with no Ext classes.
Source: Stacks Project, Cohomology, Tag 01F7; Modules, Tag 01CD.
(blueprint: lem-sc-scalar-pullback-tensor-coefficient).

Proof: Apply the inverse-image/direct-image adjunction to the two morphisms.
Precompose their underlying presheaf morphisms with the tensorator of the sheaf
inclusion. Evaluate over each open U on a pure tensor s tensor r. The defining
adjunction identity for scalarPullbackCoefficient identifies each factor with the
normalized module pullback unit applied to s or r. The section formula for
scalarTensorCoefficient sends a pure tensor to tmulSection s r. The section
normalization of module_pullback_tensor sends the unit applied to this tensor
section to the tensor of the two unit sections. The oplax comparison is the mate
of the lax tensor comparison for direct image, so its adjoint gives precisely the
same tensor of unit sections. Thus both composites agree on pure tensors. The
linear tensor universal property extends the equality to presheaf tensors, and
the sheafification adjunction extends it to the sheaf tensor. Finally injectivity
of the inverse-image adjunction gives the displayed coefficient square. Empty
schemes and zero modules require no exception: all these section identities hold.
-/
theorem scalarPullbackCoefficient_tensor
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ X) (ht : t ≫ f = g) (F G : X.Modules) :
    (scalarInverseImage t).map (scalarTensorCoefficient f F G) ≫
        scalarPullbackCoefficient f g t ht (@id X.Modules (F ⊗ G)) ≫
        scalarHom g ((Classical.choose (module_pullback_tensor t)) F G).hom =
      ((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).leftAdjointOplaxMonoidal.δ
          (scalarSheaf f F) (scalarSheaf f G) ≫
        (scalarPullbackCoefficient f g t ht F ⊗ₘ
          scalarPullbackCoefficient f g t ht G) ≫
        scalarTensorCoefficient g ((tensorPullback t).obj F)
          ((tensorPullback t).obj G) := by
  dsimp only [id]
  apply scalar_tensor_comparison_of_adjoints
  apply scalar_tensor_comparison_of_sections
  intro U s r
  erw [exists_scalarTensorCoefficient f F G U.unop s r]
  erw [scalar_pullback_adjunct_app f g t ht (F ⊗ G) U (tmulSection s r),
    scalar_pullback_adjunct_app f g t ht F U s, scalar_pullback_adjunct_app f g t ht G U r]
  exact scalar_tensor_pullback_unit g t F G U s r


end
end AlgebraicGeometry.Scheme.Modules
