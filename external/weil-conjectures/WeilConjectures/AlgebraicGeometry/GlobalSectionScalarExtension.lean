/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import WeilConjectures.AlgebraicGeometry.FunctorialRingComplexSheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules

/-!
# Scalar extension from the ring of global sections

Source: Stacks Project, algebraization.tex, Tag 099E, final paragraph.
(auxiliary; not a blueprint node).

The functor is the constant module presheaf followed by presheaf scalar extension and
module sheafification. Its map to the ring sheaf is constructed by the two adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

/-- The ring of compatible global sections, with pointwise ring operations.
Source: Stacks Project, Tag 099E.
(auxiliary; not a blueprint node). -/
def ringFamilyGlobalRing : CommRingCat.{u} :=
  let S := RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat)
  letI : CommRing S := @Subring.toCommRing _ _ S
  CommRingCat.of S

/-- Evaluation of global sections as a ring-presheaf map.
Source: Stacks Project, Tag 099E.
(auxiliary; not a blueprint node). -/
def ringFamilyGlobalEvaluation :
    (Functor.const Cᵒᵖ).obj (RingCat.of (ringFamilyGlobalRing O)) ⟶
      (𝟭 C).op ⋙ ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj where
  app X := RingCat.ofHom
    { toFun := fun s ↦ s.val X
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  naturality _ _ a := by
    ext s
    exact (s.property a).symm

/-- The given global list, regarded as elements of the global ring.
Source: Stacks Project, Tag 099E.
(auxiliary; not a blueprint node). -/
def ringFamilyGlobalList (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    Fin r → ringFamilyGlobalRing O := f

/-- The finitely generated ideal of the global ring specified by the list.
Source: Stacks Project, Tag 099E.
(auxiliary; not a blueprint node). -/
def ringFamilyGlobalIdeal (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    {I : Ideal (ringFamilyGlobalRing O) // I.FG} :=
  ⟨Ideal.span (Set.range (ringFamilyGlobalList O r f)),
    Submodule.fg_span (Set.finite_range _)⟩

/-- Evaluation extends the global generated ideal to the sectionwise generated ideal.
Source: Stacks Project, Tag 099E.
(auxiliary; not a blueprint node).
Proof: ideal map commutes with span, and the image of the global list is its value at X. -/
theorem ringFamilyGlobalIdeal_map (r : ℕ)
    (f : Fin r → (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) :
    (ringFamilyGlobalIdeal O r f).val.map ((ringFamilyGlobalEvaluation O).app X).hom =
      (ringFamilySectionIdeal O r f X).val := by
  rw [ringFamilyGlobalIdeal, Ideal.map_span, ← Set.range_comp]
  rfl

/-- Regard a one-point module as a constant module presheaf on C.
Source: Stacks Project, Tag 099E.
(auxiliary; not a blueprint node). -/
def ringFamilyConstantPresheaf : RingSiteModules (ringFamilyGlobalRing O) ⥤
    PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of (ringFamilyGlobalRing O))) where
  obj M :=
    { obj := fun _ ↦ M.val.obj (op ⟨PUnit.unit⟩)
      map := fun _ ↦ ModuleCat.ofHom LinearMap.id
      map_id := by intros; rfl
      map_comp := by intros; rfl }
  map a := { app := fun _ ↦ a.val.app (op ⟨PUnit.unit⟩) }
  map_id := by intros; rfl
  map_comp := by intros; rfl

theorem ringFamilyConstantPresheaf_additive : (ringFamilyConstantPresheaf O).Additive :=
  { map_add := by intros; rfl }

attribute [local instance] ringFamilyConstantPresheaf_additive

theorem ringFamilyGlobalPushforward_additive :
    (PresheafOfModules.pushforward (ringFamilyGlobalEvaluation O)).Additive :=
  { map_add := by intros; rfl }

attribute [local instance] ringFamilyGlobalPushforward_additive

theorem ringFamilyGlobalPullback_additive :
    (PresheafOfModules.pullback (ringFamilyGlobalEvaluation O)).Additive :=
  (PresheafOfModules.pullbackPushforwardAdjunction _).left_adjoint_additive

attribute [local instance] ringFamilyGlobalPullback_additive

/-- Extend the constant module presheaf to O and sheafify.
Source: Stacks Project, Tag 099E.
(auxiliary; not a blueprint node). -/
def ringFamilyGlobalExtension : RingSiteModules (ringFamilyGlobalRing O) ⥤
    ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) :=
  ringFamilyConstantPresheaf O ⋙
    PresheafOfModules.pullback (ringFamilyGlobalEvaluation O) ⋙
      PresheafOfModules.sheafification
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)

theorem ringFamilyGlobalExtension_additive : (ringFamilyGlobalExtension O).Additive := by
  have : (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction _).left_adjoint_additive
  unfold ringFamilyGlobalExtension
  infer_instance

attribute [local instance] ringFamilyGlobalExtension_additive

/-- Multiplication O tensor_A A to O, constructed by adjoint transposition of evaluation.
Source: Stacks Project, Tag 099E.
(auxiliary; not a blueprint node). -/
def ringFamilyGlobalExtensionUnit :
    (ringFamilyGlobalExtension O).obj (ringComplexUnit (ringFamilyGlobalRing O)) ⟶
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) := by
  let R := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let M := SheafOfModules.unit R
  let S := PresheafOfModules.sheafification (𝟙 R.obj)
  let V := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let g : (ringFamilyConstantPresheaf O).obj (ringComplexUnit (ringFamilyGlobalRing O)) ⟶
      (PresheafOfModules.pushforward (ringFamilyGlobalEvaluation O)).obj (V.obj M) :=
    { app := fun X ↦ ModuleCat.ofHom
        (X := ((ringFamilyConstantPresheaf O).obj
          (ringComplexUnit (ringFamilyGlobalRing O))).obj X)
        (Y := ((PresheafOfModules.pushforward (ringFamilyGlobalEvaluation O)).obj
          (V.obj M)).obj X)
        { toFun := fun s ↦ s.val X
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      naturality := by
        intro X Y a
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact (s.property a).symm }
  exact ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _).symm
    (((PresheafOfModules.pullbackPushforwardAdjunction
      (ringFamilyGlobalEvaluation O)).homEquiv _ _).symm g)

/-- Scalar extension of a complex over the global ring.
Source: Stacks Project, Tag 099E.
(auxiliary; not a blueprint node). -/
def ringFamilyGlobalExtensionComplex
    (P : CochainComplex (RingSiteModules (ringFamilyGlobalRing O)) ℤ) :
    ringedSiteComplex O :=
  ((ringFamilyGlobalExtension O).mapHomologicalComplex (.up ℤ)).obj P

/-- Scalar extension of the augmentation, followed by O tensor_A A = O.
Source: Stacks Project, Tag 099E.
(auxiliary; not a blueprint node). -/
def ringFamilyGlobalExtensionAugmentation
    {P : CochainComplex (RingSiteModules (ringFamilyGlobalRing O)) ℤ}
    (ε : P ⟶ ringComplexSingle (ringFamilyGlobalRing O)) :
    ringFamilyGlobalExtensionComplex O P ⟶ ringedSiteRingComplex O :=
  ((ringFamilyGlobalExtension O).mapHomologicalComplex (.up ℤ)).map ε ≫
    ((HomologicalComplex.singleMapHomologicalComplex (ringFamilyGlobalExtension O)
      (.up ℤ) 0).app (ringComplexUnit (ringFamilyGlobalRing O))).hom ≫
    (HomologicalComplex.single _ (.up ℤ) 0).map (ringFamilyGlobalExtensionUnit O)

end CategoryTheory
