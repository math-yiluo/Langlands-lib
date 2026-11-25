/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Constant vector-space coefficients extended to the structure presheaf

Source: Stacks Project, Varieties, Tag 0BED, degree-zero tensor calculation.
The construction is extension of scalars of a constant presheaf, followed by
pointwise tensor with the coefficient presheaf. No choice of a basis enters it.
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The constant ring map induced by the structure morphism.
Source: Stacks Project, Varieties, Tag 0BED, scalar coefficients in the ordinary
pushforward tensor formula.
(blueprint: lem-sc-picard-constant-sections-tensor-basis). -/
def picardConstantRingMap (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) :
    (Functor.const Y.Opensᵒᵖ).obj (RingCat.of k) ⟶
      (𝟭 Y.Opens).op ⋙ Y.ringCatSheaf.obj where
  app U := RingCat.ofHom (scalarMap g U.unop)
  naturality U V i := by
    ext r
    change scalarMap g V.unop r = (Y.presheaf.map i).hom (scalarMap g U.unop r)
    simp only [scalarMap, RingHom.comp_apply]
    change _ = (Y.presheaf.map (homOfLE (le_top (a := U.unop))).op ≫
      Y.presheaf.map i) _
    rw [← Y.presheaf.map_comp]
    rfl

/-- The constant presheaf of vector spaces as modules over the constant ring.
Source: Stacks Project, Varieties, Tag 0BED, constant Gamma(X,F) coefficients.
(blueprint: lem-sc-picard-constant-sections-tensor-basis). -/
def picardConstantVector (k : Type w) [Field k] (Y : Scheme.{w}) (M : ModuleCat.{w} k) :
    _root_.PresheafOfModules ((Functor.const Y.Opensᵒᵖ).obj (RingCat.of k)) where
  obj _ := M
  map _ := ModuleCat.ofHom (LinearMap.id)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- Extend the constant vector space to O_Y, then tensor it with G, pointwise.
Source: Stacks Project, Varieties, Tag 0BED, ordinary pushforward tensor coefficients.
(blueprint: lem-sc-picard-constant-sections-tensor-basis). -/
def picardConstantSectionsTensor (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) (G : Y.Modules) :
    _root_.PresheafOfModules Y.ringCatSheaf.obj :=
  ((PresheafOfModules.pullback (picardConstantRingMap k Y g)).obj
    (picardConstantVector k Y M)) ⊗ G.val


private def constantBasisIso (k : Type w) [Field k] (Y : Scheme.{w})
    (M : ModuleCat.{w} k) (I : Type w) (b : Module.Basis I k M) :
    (PresheafOfModules.free ((Functor.const Y.Opensᵒᵖ).obj (RingCat.of k))).obj
      ((Functor.const Y.Opensᵒᵖ).obj I) ≅ picardConstantVector k Y M :=
  PresheafOfModules.isoMk (fun _ ↦ b.repr.symm.toModuleIso) (by
    intro U V f
    apply ModuleCat.free_hom_ext
    intro i
    simp [PresheafOfModules.free, PresheafOfModules.freeObj, picardConstantVector]
    rfl)

private def scalarExtensionFreeIso (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) :
    PresheafOfModules.free ((Functor.const Y.Opensᵒᵖ).obj (RingCat.of k)) ⋙
      PresheafOfModules.pullback (picardConstantRingMap k Y g) ≅
        PresheafOfModules.free Y.ringCatSheaf.obj :=
  ((PresheafOfModules.freeAdjunction _).comp
    (PresheafOfModules.pullbackPushforwardAdjunction (picardConstantRingMap k Y g))).leftAdjointUniq
      (PresheafOfModules.freeAdjunction _)

private def freeConstantCofan {C : Type w} [SmallCategory C]
    (R : Cᵒᵖ ⥤ RingCat.{w}) (I : Type w) :
    Cofan (fun _ : I ↦ PresheafOfModules.unit R) :=
  Cofan.mk ((PresheafOfModules.free R).obj ((Functor.const Cᵒᵖ).obj I))
    (fun i ↦ (PresheafOfModules.unitHomEquiv _).symm
      (PresheafOfModules.sectionsMk (fun _ ↦ ModuleCat.freeMk i) (by
        intro U V f
        exact ModuleCat.freeDesc_apply _ i)))

private lemma freeConstantCofan_inj_one {C : Type w} [SmallCategory C]
    (R : Cᵒᵖ ⥤ RingCat.{w}) (I : Type w) (i : I) (U : Cᵒᵖ) :
    ((freeConstantCofan R I).inj i).app U (1 : R.obj U) = ModuleCat.freeMk i := by
  exact congrArg (fun s ↦ s.val U)
    ((PresheafOfModules.unitHomEquiv (freeConstantCofan R I).pt).apply_symm_apply
      (PresheafOfModules.sectionsMk (M := (freeConstantCofan R I).pt)
        (fun _ ↦ ModuleCat.freeMk i) (by
        intro X Y f
        exact ModuleCat.freeDesc_apply _ i)))

private def freeConstantDesc {C : Type w} [SmallCategory C]
    (R : Cᵒᵖ ⥤ RingCat.{w}) (I : Type w)
    (t : Cofan (fun _ : I ↦ PresheafOfModules.unit R)) :
    (freeConstantCofan R I).pt ⟶ t.pt :=
  PresheafOfModules.freeObjDesc
    { app := fun U ↦ ↾fun i ↦ (t.inj i).app U (1 : R.obj U)
      naturality := fun U V f ↦ by
        ext i
        exact ((PresheafOfModules.unitHomEquiv t.pt) (t.inj i)).property f |>.symm }

private def freeConstantIsColimit {C : Type w} [SmallCategory C]
    (R : Cᵒᵖ ⥤ RingCat.{w}) (I : Type w) :
    IsColimit (freeConstantCofan R I) := by
  refine Cofan.IsColimit.mk _ (freeConstantDesc R I) ?_ ?_
  · intro t i
    apply (PresheafOfModules.unitHomEquiv t.pt).injective
    ext U
    change (freeConstantDesc R I t).app U
      (((freeConstantCofan R I).inj i).app U (1 : R.obj U)) =
        (t.inj i).app U (1 : R.obj U)
    rw [freeConstantCofan_inj_one]
    exact ModuleCat.freeDesc_apply _ i
  · intro t m hm
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.free_hom_ext
    intro i
    have h := congrArg (fun a ↦ (a.app U).hom (1 : R.obj U)) (hm i)
    change (m.app U).hom (((freeConstantCofan R I).inj i).app U (1 : R.obj U)) =
      (t.inj i).app U (1 : R.obj U) at h
    rw [freeConstantCofan_inj_one] at h
    exact h.trans (ModuleCat.freeDesc_apply
      (↾fun j ↦ (t.inj j).app U (1 : R.obj U)) i).symm

/-- A prescribed basis identifies the tensor coefficient presheaf with a coproduct.
Source: Stacks Project, Varieties, Tag 0BED, the second isomorphism in the
ordinary direct-image calculation.
(blueprint: lem-sc-picard-constant-sections-tensor-basis).

Proof: The constant vector presheaf sends each open to M with identity restriction.
The basis identifies it with the coproduct of I copies of the constant k-module k:
on sections the map sends the i-th coefficient a to a times b_i, and the inverse
is b.repr. Constant-presheaf coproducts are pointwise, and these maps commute with
identity restriction. Extension of scalars is the left adjoint to restriction along
the constant ring map, so preserves this coproduct and takes the constant k-module k
to the unit O_Y presheaf. This last identification follows by their identical
Hom universal properties: both represent sections of the underlying presheaf.
Tensor with G preserves coproducts, pointwise. The left unitors identify every
O_Y tensor G summand with G. Composing these three isomorphisms gives the result.
This uses no geometry or quasi-coherence. An empty basis is a zero vector space;
extension and tensor preserve its initial object, so the same argument covers it. -/
theorem exists_picard_constant_sections_tensor_basis
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) (G : Y.Modules)
    (I : Type w) (b : Module.Basis I k M) :
    Nonempty ((∐ fun _ : I ↦ G.val) ≅ picardConstantSectionsTensor k Y g M G) := by
  let R := Y.ringCatSheaf.obj
  let F := PresheafOfModules.pullback (picardConstantRingMap k Y g)
  let e : (∐ fun _ : I ↦ PresheafOfModules.unit R) ≅
      F.obj (picardConstantVector k Y M) :=
    (colimit.isColimit _).coconePointUniqueUpToIso (freeConstantIsColimit R I) ≪≫
      ((scalarExtensionFreeIso k Y g).app ((Functor.const Y.Opensᵒᵖ).obj I)).symm ≪≫
        F.mapIso (constantBasisIso k Y M I b)
  have : PreservesColimitsOfSize.{w, w}
      (CategoryTheory.MonoidalCategory.tensorRight G.val) := by
    change PreservesColimitsOfSize.{w, w}
      (CategoryTheory.MonoidalCategory.tensorRight
        (C := _root_.PresheafOfModules.{w}
          (Y.presheaf ⋙ forget₂ CommRingCat RingCat)) G.val)
    infer_instance
  exact ⟨Sigma.mapIso (fun _ : I ↦ (λ_ G.val).symm) ≪≫
    (PreservesCoproduct.iso (CategoryTheory.MonoidalCategory.tensorRight G.val)
      (fun _ : I ↦ PresheafOfModules.unit R)).symm ≪≫
        CategoryTheory.MonoidalCategory.tensorIso e (Iso.refl G.val)⟩

end
end AlgebraicGeometry.Scheme.Modules
