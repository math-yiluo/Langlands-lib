/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FunctorialRingComplexSheaf
import WeilConjectures.CategoryTheory.ModuleSheafificationLocalIso

/-! # Augmented ring-family models for locally equal section ideals

Source: Stacks Project, Tag 099E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite AlgebraicGeometry
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})
variable (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
variable (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
variable (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections)

/-- Transport a component of the ring-complex family along equality of ideals.
Source: Stacks Project, Tag 099E.
(auxiliary; not a blueprint node). -/
def ringFamilyComponentEquiv (A : CommRingCat.{u})
    (I I' : {I : Ideal A // I.FG}) (h : I = I') (n : ℤ) :
    ((K A I).X n).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A]
      ((K A I').X n).val.obj (op ⟨PUnit.unit⟩) :=
  (eqToIso (congrArg (fun L ↦ ((K A L).X n).val.obj (op ⟨PUnit.unit⟩)) h)).toLinearEquiv

private theorem ringFamilyComponentEquiv_map
    (A B : CommRingCat.{u}) (φ : A →+* B)
    (I I' : {I : Ideal A // I.FG}) (L L' : {L : Ideal B // L.FG})
    (hI : I = I') (hL : L = L')
    (h : I.val.map φ = L.val) (h' : I'.val.map φ = L'.val)
    (n : ℤ) (x : ((K A I).X n).val.obj (op ⟨PUnit.unit⟩)) :
    ringFamilyComponentEquiv K B L L' hL n (m A B φ I L h n x) =
      m A B φ I' L' h' n (ringFamilyComponentEquiv K A I I' hI n x) := by
  subst I'
  subst L'
  rfl

private theorem ringFamilyComponentEquiv_d
    (A : CommRingCat.{u}) (I I' : {I : Ideal A // I.FG}) (h : I = I')
    (n k : ℤ) (x : ((K A I).X n).val.obj (op ⟨PUnit.unit⟩)) :
    ringFamilyComponentEquiv K A I I' h k (((K A I).d n k).val.app _ x) =
      ((K A I').d n k).val.app _ (ringFamilyComponentEquiv K A I I' h n x) := by
  subst I'
  rfl

private theorem ringFamilyComponentEquiv_augmentation
    (A : CommRingCat.{u}) (I I' : {I : Ideal A // I.FG}) (h : I = I')
    (x : ((K A I).X 0).val.obj (op ⟨PUnit.unit⟩)) :
    ((ε A I').f 0).val.app _ (ringFamilyComponentEquiv K A I I' h 0 x) =
      ((ε A I).f 0).val.app _ x := by
  subst I'
  rfl

/-- The augmented sheafification evaluates on presheaf-unit sections as its original
presheaf augmentation.
Source: Stacks Project, Tag 099E.
(auxiliary; not a blueprint node).
Proof: evaluate the inverse equation for the sheafification adjunction on complexes. -/
theorem ringFamilySheafModel_augmentation_unit
    (n : ℤ) (X : Cᵒᵖ)
    (x : ((ringFamilyPresheafComplex O K ε m hm r f).X n).obj X) :
    ((ringFamilySheafModel O K ε m hm r f).2.f n).val.app X
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app
            ((ringFamilyPresheafComplex O K ε m hm r f).X n)).app X x) =
      ((ringFamilyPresheafAugmentation O K ε m hm r f).f n).app X x := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)
  let S := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)
  let : S.Additive := adj.left_adjoint_additive
  have h := ((adj.mapHomologicalComplex (.up ℤ)).homEquiv
    (ringFamilyPresheafComplex O K ε m hm r f) (ringedSiteRingComplex O)).apply_symm_apply
      (ringFamilyPresheafAugmentation O K ε m hm r f)
  exact congrArg (fun z ↦ (z.f n).app X x) h

/-- Locally equal generated section ideals give canonically isomorphic augmented models.
Source: Stacks Project, Tag 099E, independence of the choice of finite generating ideal.
(auxiliary; not a blueprint node).

Proof: equality of the two section ideals is stable under restriction, since both ideal
families commute with extension of scalars. On that locus the ring-family components,
differentials and augmentations agree by transport along equality of ideals. The assumed
coverings make the locus locally exhaustive. Apply the augmented module-sheafification
local-isomorphism theorem. -/
theorem ringFamilySheafModel_iso_of_locally_equal_ideals_with_unit (s : ℕ)
    (g : Fin s → (O.obj ⋙ forget CommRingCat).sections)
    (h : ∀ X : C, ∃ S ∈ J X, ∀ (Y : C) (a : Y ⟶ X), S a →
      (ringFamilySectionIdeal O r f (op Y)).val =
        (ringFamilySectionIdeal O s g (op Y)).val) :
    ∃ z : (ringFamilySheafModel O K ε m hm r f).1 ≅
        (ringFamilySheafModel O K ε m hm s g).1,
      z.hom ≫ (ringFamilySheafModel O K ε m hm s g).2 =
        (ringFamilySheafModel O K ε m hm r f).2 ∧
        ∀ (n : ℤ) (X : Cᵒᵖ)
          (hX : ringFamilySectionIdeal O r f X = ringFamilySectionIdeal O s g X)
          (x : ((ringFamilyPresheafComplex O K ε m hm r f).X n).obj X),
          (z.hom.f n).val.app X
              (((PresheafOfModules.sheafificationAdjunction
                (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app
                  ((ringFamilyPresheafComplex O K ε m hm r f).X n)).app X x) =
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app
                ((ringFamilyPresheafComplex O K ε m hm s g).X n)).app X
                  (ringFamilyComponentEquiv K (O.obj.obj X) _ _ hX n x)) := by
  let E : Cᵒᵖ → Prop := fun X ↦ ringFamilySectionIdeal O r f X =
    ringFamilySectionIdeal O s g X
  have hE {X Y : Cᵒᵖ} (a : X ⟶ Y) (hX : E X) : E Y := by
    apply Subtype.ext
    exact (ringFamilySectionIdeal_map O r f a).symm.trans
      ((congrArg (fun L : {I : Ideal (O.obj.obj X) // I.FG} ↦
        L.val.map (O.obj.map a).hom) hX).trans (ringFamilySectionIdeal_map O s g a))
  have hcover : ∀ X : C, ∃ S ∈ J X, ∀ (Y : C) (a : Y ⟶ X), S a → E (op Y) := by
    intro X
    obtain ⟨S, hS, hs⟩ := h X
    exact ⟨S, hS, fun Y a ha ↦ Subtype.ext (hs Y a ha)⟩
  let e : ∀ (n : ℤ) (X : Cᵒᵖ), E X →
      ((ringFamilyPresheafComplex O K ε m hm r f).X n).obj X ≃ₗ[O.obj.obj X]
        ((ringFamilyPresheafComplex O K ε m hm s g).X n).obj X :=
    fun n X hX ↦ ringFamilyComponentEquiv K (O.obj.obj X) _ _ hX n
  apply PresheafOfModules.exists_augmentedSheafificationIso_of_localEquiv_with_unit E hE
    (ringFamilyPresheafComplex O K ε m hm r f)
    (ringFamilyPresheafComplex O K ε m hm s g) (ringedSiteRingComplex O)
    (ringFamilySheafModel O K ε m hm r f).2
    (ringFamilySheafModel O K ε m hm s g).2 hcover e
  · intro n X Y a hX x
    exact ringFamilyComponentEquiv_map K m (O.obj.obj X) (O.obj.obj Y)
      (O.obj.map a).hom _ _ _ _ hX (hE a hX)
      (ringFamilySectionIdeal_map O r f a) (ringFamilySectionIdeal_map O s g a) n x
  · intro n k X hX x
    exact ringFamilyComponentEquiv_d K (O.obj.obj X) _ _ hX n k x
  · intro n X hX x
    have hG := ringFamilySheafModel_augmentation_unit O K ε m hm s g n X (e n X hX x)
    have hF := ringFamilySheafModel_augmentation_unit O K ε m hm r f n X x
    refine hG.trans (Eq.trans ?_ hF.symm)
    unfold ringFamilyPresheafAugmentation
    simp only [HomologicalComplex.comp_f, PresheafOfModules.comp_app,
      ConcreteCategory.comp_apply]
    apply congrArg
    by_cases hn : n = 0
    · subst n
      simp only [HomologicalComplex.mkHomToSingle_f, PresheafOfModules.comp_app,
        ConcreteCategory.comp_apply]
      apply congrArg
      change (ringFamilyPresheafAugmentationZero O K ε m hm s g).app X
        (ringFamilyComponentEquiv K (O.obj.obj X) _ _ hX 0 x) =
          (ringFamilyPresheafAugmentationZero O K ε m hm r f).app X x
      change ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (ringComplexUnit (O.obj.obj X))).hom).val.app (op ⟨PUnit.unit⟩)
          (((ε (O.obj.obj X) (ringFamilySectionIdeal O s g X)).f 0).val.app _
            (ringFamilyComponentEquiv K (O.obj.obj X) _ _ hX 0 x)) = _
      exact congrArg _ (ringFamilyComponentEquiv_augmentation K ε
        (O.obj.obj X) _ _ hX x)
    · simp only [HomologicalComplex.mkHomToSingle, dite_eq_right hn]
      rfl

end CategoryTheory
