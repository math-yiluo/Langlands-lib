/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexCechData
import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Algebra.Homology.RingHomExtensionTransport

/-! # The scalar-extension chain map induced by a semilinear chain map

Source: Stacks Project, Tag 099D(c); Modules on Sites, Tag 03EK.
All data are constructed by the extension/restriction adjunction, rather than chosen
from an existence assertion.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry
noncomputable section

def ringComplexPointLift {A : CommRingCat.{u}} (M N : RingSiteModules A)
    (f : M.val.obj (op ⟨PUnit.unit⟩) →ₗ[A] N.val.obj (op ⟨PUnit.unit⟩)) : M ⟶ N where
  val :=
    { app := fun U ↦ by
        have hU : U = op ⟨PUnit.unit⟩ := Subsingleton.elim _ _
        subst U
        exact ModuleCat.ofHom f
      naturality := by
        intro U V i
        have hU : U = op ⟨PUnit.unit⟩ := Subsingleton.elim _ _
        subst U
        have hV : V = op ⟨PUnit.unit⟩ := Subsingleton.elim _ _
        subst V
        have hi : i = 𝟙 (op (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1})) :=
          Subsingleton.elim _ _
        subst i
        ext x
        simp }

def ringComplexExtensionPresheaf {A B : CommRingCat.{u}} (φ : A →+* B) :
    RingSiteModules A ⥤ PresheafOfModules.{u} ((sheafCompose ⊥
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (CochainComplex.onePointRingSheaf B)).obj where
  obj := SheafOfModules.changeOfRingsPresheaf.{u, u, u} (ringSiteMap φ)
  map a :=
    { app := fun U ↦ (ModuleCat.extendScalars ((ringSiteMap φ).hom.app U).hom).map
        (a.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality (ringSiteMap φ) _ a }
  map_id := by
    intro M
    apply PresheafOfModules.hom_ext
    intro U
    simp
    rfl
  map_comp := by
    intro M N P a b
    apply PresheafOfModules.hom_ext
    intro U
    simp

/-- Termwise scalar extension on the one-object ring site, with its actual morphisms.
Source: Stacks Project, Tags 099D(c), 03EK.
(auxiliary; not a blueprint node). -/
def ringComplexExtension {A B : CommRingCat.{u}} (φ : A →+* B) :
    RingSiteModules A ⥤ RingSiteModules B :=
  ringComplexExtensionPresheaf φ ⋙ PresheafOfModules.sheafification
    (𝟙 ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf B)).obj)

instance ringComplexExtension_additive {A B : CommRingCat.{u}} (φ : A →+* B) :
    (ringComplexExtension φ).Additive := by
  have hscalar (U : (Discrete PUnit.{u + 1})ᵒᵖ) :
      (ModuleCat.extendScalars ((ringSiteMap φ).hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj ((ringSiteMap φ).hom.app U).hom).left_adjoint_additive
  have hsheaf : (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf B)).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction _).left_adjoint_additive
  have hpre : (ringComplexExtensionPresheaf φ).Additive := by
    constructor
    intro M N a b
    apply PresheafOfModules.hom_ext
    intro U
    simpa only [ringComplexExtensionPresheaf, SheafOfModules.add_val,
      PresheafOfModules.add_app] using
      (ModuleCat.extendScalars ((ringSiteMap φ).hom.app U).hom).map_add
        (f := a.val.app U) (g := b.val.app U)
  unfold ringComplexExtension
  infer_instance

/-- The scalar-extension complex, formed by applying the actual additive functor. -/
def ringComplexExtensionComplex {A B : CommRingCat.{u}} (φ : A →+* B)
    (P : CochainComplex (RingSiteModules A) ℤ) : CochainComplex (RingSiteModules B) ℤ :=
  ((ringComplexExtension φ).mapHomologicalComplex (.up ℤ)).obj P

/-- The sheafification unit identifies sections of scalar extension with the tensor product.
The topology is bottom, so the unit is an isomorphism. -/
def ringComplexExtensionSections {A B : CommRingCat.{u}} (φ : A →+* B)
    (M : RingSiteModules A) :
    (ModuleCat.extendScalars φ).obj (M.val.obj (op ⟨PUnit.unit⟩)) ≅
      ((ringComplexExtension φ).obj M).val.obj (op ⟨PUnit.unit⟩) := by
  let T := SheafOfModules.changeOfRingsPresheaf.{u, u, u} (ringSiteMap φ) M
  let η := toSheafify ⊥ T.presheaf
  have : IsIso η := isIso_toSheafify ⊥ (Presheaf.isSheaf_bot _)
  let e : (ModuleCat.extendScalars φ).obj (M.val.obj (op ⟨PUnit.unit⟩)) →ₗ[B]
      ((ringComplexExtension φ).obj M).val.obj (op ⟨PUnit.unit⟩) :=
    (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app T).app
      (op ⟨PUnit.unit⟩)).hom
  exact (LinearEquiv.ofBijective e
    (ConcreteCategory.bijective_of_isIso (η.app (op ⟨PUnit.unit⟩)))).toModuleIso

/-- Extend a semilinear map by `b ⊗ x ↦ b • f x`, on the one-object site. -/
def ringComplexSemilinearLift {A B : CommRingCat.{u}} (φ : A →+* B)
    (M : RingSiteModules A) (N : RingSiteModules B)
    (f : M.val.obj (op ⟨PUnit.unit⟩) →ₛₗ[φ] N.val.obj (op ⟨PUnit.unit⟩)) :
    (ringComplexExtension φ).obj M ⟶ N :=
  ringComplexPointLift _ _ (((ringComplexExtensionSections φ M).inv ≫
    ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm
      ((ModuleCat.semilinearMapAddEquiv φ _ _) f)).hom)

/-- The extension lift has the required normalization on pure tensors. -/
theorem ringComplexSemilinearLift_one_tmul {A B : CommRingCat.{u}} (φ : A →+* B)
    (M : RingSiteModules A) (N : RingSiteModules B)
    (f : M.val.obj (op ⟨PUnit.unit⟩) →ₛₗ[φ] N.val.obj (op ⟨PUnit.unit⟩))
    (x : M.val.obj (op ⟨PUnit.unit⟩)) :
    (ringComplexSemilinearLift φ M N f).val.app (op ⟨PUnit.unit⟩)
      ((toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf
        (ringSiteMap φ) M).presheaf).app (op ⟨PUnit.unit⟩)
        ((1 : B) ⊗ₜ[A, φ] x)) = f x := by
  let e := ringComplexExtensionSections φ M
  have he : e.hom ((1 : B) ⊗ₜ[A, φ] x) =
      (toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf
        (ringSiteMap φ) M).presheaf).app (op ⟨PUnit.unit⟩)
        ((1 : B) ⊗ₜ[A, φ] x) := rfl
  rw [← he]
  change (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm
    ((ModuleCat.semilinearMapAddEquiv φ _ _) f))
      (e.inv (e.hom ((1 : B) ⊗ₜ[A, φ] x))) = _
  have hi (z : (ModuleCat.extendScalars φ).obj (M.val.obj (op ⟨PUnit.unit⟩))) :
      e.inv (e.hom z) = z := ConcreteCategory.congr_hom e.hom_inv_id z
  rw [hi]
  have h := congrArg (fun g ↦ g x)
    (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).apply_symm_apply
      ((ModuleCat.semilinearMapAddEquiv φ _ _) f))
  exact h

/-- A module-sheaf morphism on the one-object site is determined by its section map. -/
theorem ringComplex_point_hom_ext {A : CommRingCat.{u}} {M N : RingSiteModules A}
    {f g : M ⟶ N}
    (h : f.val.app (op ⟨PUnit.unit⟩) = g.val.app (op ⟨PUnit.unit⟩)) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rw [CategoryTheory.point_eq U]
  exact h

/-- Pure tensors with first coordinate one determine a scalar-extension morphism. -/
theorem ringComplexExtension_hom_ext {A B : CommRingCat.{u}} (φ : A →+* B)
    (M : RingSiteModules A) (N : RingSiteModules B)
    {f g : (ringComplexExtension φ).obj M ⟶ N}
    (h : ∀ x : M.val.obj (op ⟨PUnit.unit⟩),
      f.val.app (op ⟨PUnit.unit⟩)
          ((toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf
            (ringSiteMap φ) M).presheaf).app (op ⟨PUnit.unit⟩)
            ((1 : B) ⊗ₜ[A, φ] x)) =
        g.val.app (op ⟨PUnit.unit⟩)
          ((toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf
            (ringSiteMap φ) M).presheaf).app (op ⟨PUnit.unit⟩)
            ((1 : B) ⊗ₜ[A, φ] x))) : f = g := by
  apply ringComplex_point_hom_ext
  apply (cancel_epi (ringComplexExtensionSections φ M).hom).1
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact h x

/-- Scalar extension of a morphism sends `1 ⊗ x` to `1 ⊗ a x`. -/
theorem ringComplexExtension_map_one_tmul {A B : CommRingCat.{u}} (φ : A →+* B)
    {M N : RingSiteModules A} (a : M ⟶ N) (x : M.val.obj (op ⟨PUnit.unit⟩)) :
    ((ringComplexExtension φ).map a).val.app (op ⟨PUnit.unit⟩)
      ((toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf
        (ringSiteMap φ) M).presheaf).app (op ⟨PUnit.unit⟩)
        ((1 : B) ⊗ₜ[A, φ] x)) =
      (toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf
        (ringSiteMap φ) N).presheaf).app (op ⟨PUnit.unit⟩)
        ((1 : B) ⊗ₜ[A, φ] (a.val.app (op ⟨PUnit.unit⟩) x)) := by
  let α := (PresheafOfModules.toPresheaf _).map
    ((ringComplexExtensionPresheaf φ).map a)
  have hn := congr_app (toSheafify_naturality (J := ⊥) α) (op ⟨PUnit.unit⟩)
  let : Module A B := Module.compHom B φ
  have hv := congrArg (fun f ↦ f ((1 : B) ⊗ₜ[A] x)) hn
  exact hv.symm

/-- Extend a degreewise semilinear chain map, with the prescribed tensor differential. -/
def ringComplexExtendMap {A B : CommRingCat.{u}} (φ : A →+* B)
    (P : CochainComplex (RingSiteModules A) ℤ)
    (L : CochainComplex (RingSiteModules B) ℤ)
    (f : ∀ n : ℤ, (P.X n).val.obj (op ⟨PUnit.unit⟩) →ₛₗ[φ]
      (L.X n).val.obj (op ⟨PUnit.unit⟩))
    (hf : ∀ (n k : ℤ) (x : (P.X n).val.obj (op ⟨PUnit.unit⟩)),
      f k ((P.d n k).val.app (op ⟨PUnit.unit⟩) x) =
        (L.d n k).val.app (op ⟨PUnit.unit⟩) (f n x)) :
    ringComplexExtensionComplex φ P ⟶ L where
  f n := ringComplexSemilinearLift φ (P.X n) (L.X n) (f n)
  comm' n k _ := by
    apply ringComplexExtension_hom_ext φ (P.X n) (L.X k)
    intro x
    change (L.d n k).val.app (op ⟨PUnit.unit⟩)
        ((ringComplexSemilinearLift φ (P.X n) (L.X n) (f n)).val.app _ _) =
      (ringComplexSemilinearLift φ (P.X k) (L.X k) (f k)).val.app _
        (((ringComplexExtension φ).map (P.d n k)).val.app _ _)
    rw [ringComplexSemilinearLift_one_tmul, ringComplexExtension_map_one_tmul,
      ringComplexSemilinearLift_one_tmul]
    exact (hf n k x).symm

/-- Precompose the semilinear chain map before extending scalars. -/
def ringComplexExtendAlong {A B : CommRingCat.{u}} (φ : A →+* B)
    (K : RingComplexFamily.{u}) (m : RingComplexMaps K)
    (A₀ : {I : Ideal A // I.FG}) (B₀ : {I : Ideal B // I.FG})
    (h : A₀.val.map φ = B₀.val)
    (hc : ∀ (n k : ℤ) (x : ((K A A₀).X n).val.obj (op ⟨PUnit.unit⟩)),
      m A B φ A₀ B₀ h k (((K A A₀).d n k).val.app (op ⟨PUnit.unit⟩) x) =
        ((K B B₀).d n k).val.app (op ⟨PUnit.unit⟩) (m A B φ A₀ B₀ h n x))
    (P : CochainComplex (RingSiteModules A) ℤ) (p : P ⟶ K A A₀) :
    ringComplexExtensionComplex φ P ⟶ K B B₀ :=
  ringComplexExtendMap φ P (K B B₀)
    (fun n ↦
      { toFun := fun x ↦ m A B φ A₀ B₀ h n ((p.f n).val.app (op ⟨PUnit.unit⟩) x)
        map_add' := by intros; simp
        map_smul' := by
          intro a x
          change m A B φ A₀ B₀ h n ((p.f n).val.app _ (a • x)) = _
          rw [map_smul, map_smulₛₗ] })
    (by
      intro n k x
      have hp := ConcreteCategory.congr_hom
        (congrArg (fun t ↦ t.val.app (op ⟨PUnit.unit⟩)) (p.comm n k).symm) x
      change (p.f k).val.app (op ⟨PUnit.unit⟩)
          ((P.d n k).val.app (op ⟨PUnit.unit⟩) x) =
        ((K A A₀).d n k).val.app (op ⟨PUnit.unit⟩)
          ((p.f n).val.app (op ⟨PUnit.unit⟩) x) at hp
      change m A B φ A₀ B₀ h k
          ((p.f k).val.app (op ⟨PUnit.unit⟩) ((P.d n k).val.app (op ⟨PUnit.unit⟩) x)) = _
      rw [hp]
      exact hc n k _)

/-- The extended composite has the required pure-tensor normalization. -/
theorem ringComplexExtendAlong_one_tmul {A B : CommRingCat.{u}} (φ : A →+* B)
    (K : RingComplexFamily.{u}) (m : RingComplexMaps K)
    (A₀ : {I : Ideal A // I.FG}) (B₀ : {I : Ideal B // I.FG})
    (h : A₀.val.map φ = B₀.val)
    (hc : ∀ (n k : ℤ) (x : ((K A A₀).X n).val.obj (op ⟨PUnit.unit⟩)),
      m A B φ A₀ B₀ h k (((K A A₀).d n k).val.app (op ⟨PUnit.unit⟩) x) =
        ((K B B₀).d n k).val.app (op ⟨PUnit.unit⟩) (m A B φ A₀ B₀ h n x))
    (P : CochainComplex (RingSiteModules A) ℤ) (p : P ⟶ K A A₀) (n : ℤ)
    (x : (P.X n).val.obj (op ⟨PUnit.unit⟩)) :
    ((ringComplexExtendAlong φ K m A₀ B₀ h hc P p).f n).val.app (op ⟨PUnit.unit⟩)
        ((toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf (ringSiteMap φ)
          (P.X n)).presheaf).app (op ⟨PUnit.unit⟩) ((1 : B) ⊗ₜ[A, φ] x)) =
      m A B φ A₀ B₀ h n ((p.f n).val.app (op ⟨PUnit.unit⟩) x) := by
  exact ringComplexSemilinearLift_one_tmul φ (P.X n) ((K B B₀).X n) _ x

end
end AlgebraicGeometry
