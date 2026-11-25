/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PinnedPullbackCounitShifts
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-! # Shift compatibility of the pinned tensor counit on singles
Source: Stacks Project, Tags 08HY and 0D5S; Mathlib single-functor shifts.
(blueprint: lem-pc-pinned-single-tensor-shifts). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Functor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section


namespace CategoryTheory.SingleFunctors

/-- Precomposition preserves the single-functor shift comparisons.
(blueprint: lem-pc-pinned-single-tensor-shifts)
-/
def precomp {A B C : Type*} [Category A] [Category B] [Category C] [HasShift C ℤ]
    (F : SingleFunctors B C ℤ) (T : A ⥤ B) : SingleFunctors A C ℤ where
  functor n := T ⋙ F.functor n
  shiftIso k i j h := Functor.associator _ _ _ ≪≫ isoWhiskerLeft T (F.shiftIso k i j h)
  shiftIso_zero i := by
    ext X
    simp [F.shiftIso_zero]
  shiftIso_add k l i j m h h' := by
    ext X
    simpa using F.shiftIso_add_hom_app k l i j m h h' (T.obj X)

/-- Postcomposition of a family morphism by a shift-compatible functor.
(blueprint: lem-pc-pinned-single-tensor-shifts)
-/
def postcompHom {A B C : Type*} [Category A] [Category B] [Category C]
    [HasShift B ℤ] [HasShift C ℤ] {F G : SingleFunctors A B ℤ}
    (τ : F ⟶ G) (T : B ⥤ C) [T.CommShift ℤ] : F.postcomp T ⟶ G.postcomp T where
  hom n := Functor.whiskerRight (τ.hom n) T
  comm k i j h := by
    ext X
    simp only [SingleFunctors.postcomp_shiftIso_hom_app, NatTrans.comp_app,
      Functor.whiskerRight_app, Category.assoc]
    change (T.commShiftIso k).inv.app ((F.functor j).obj X) ≫
        T.map ((F.shiftIso k i j h).hom.app X) ≫ T.map ((τ.hom i).app X) =
      (shiftFunctor C k).map (T.map ((τ.hom j).app X)) ≫
        (T.commShiftIso k).inv.app ((G.functor j).obj X) ≫
          T.map ((G.shiftIso k i j h).hom.app X)
    have hc := congr_app (τ.comm k i j h) X
    simp only [Functor.whiskerRight_app, NatTrans.comp_app] at hc
    rw [← T.map_comp, hc, T.map_comp]
    rw [← T.commShiftIso_inv_naturality_assoc]

/-- A shift-compatible transformation induces a morphism of postcomposed families.
(blueprint: lem-pc-pinned-single-tensor-shifts)
-/
def postcompNatTrans {A B C : Type*} [Category A] [Category B] [Category C]
    [HasShift B ℤ] [HasShift C ℤ] (F : SingleFunctors A B ℤ)
    {T U : B ⥤ C} [T.CommShift ℤ] [U.CommShift ℤ]
    (τ : T ⟶ U) [NatTrans.CommShift τ ℤ] : F.postcomp T ⟶ F.postcomp U where
  hom n := Functor.whiskerLeft (F.functor n) τ
  comm k i j h := by
    ext X
    simp only [SingleFunctors.postcomp_shiftIso_hom_app, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
    change (T.commShiftIso k).inv.app ((F.functor j).obj X) ≫
        T.map ((F.shiftIso k i j h).hom.app X) ≫ τ.app ((F.functor i).obj X) =
      (shiftFunctor C k).map (τ.app ((F.functor j).obj X)) ≫
        (U.commShiftIso k).inv.app ((F.functor j).obj X) ≫
          U.map ((F.shiftIso k i j h).hom.app X)
    rw [τ.naturality]
    simp only [NatTrans.shift_app τ k, Category.assoc, Iso.hom_inv_id_app_assoc]

/-- Precomposition and shift-compatible postcomposition commute.
(blueprint: lem-pc-pinned-single-tensor-shifts)
-/
def precompPostcompIso {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] (F : SingleFunctors B C ℤ)
    (T : A ⥤ B) (U : C ⥤ D) [U.CommShift ℤ] :
    (F.precomp T).postcomp U ≅ (F.postcomp U).precomp T :=
  SingleFunctors.isoMk (fun n ↦ Functor.associator _ _ _) (fun k i j h ↦ by
    ext X
    simp [precomp, SingleFunctors.postcomp_shiftIso_hom_app])

/-- The termwise mapped-single comparison as an isomorphism of families.
(blueprint: lem-pc-pinned-single-tensor-shifts)
-/
def mappedCochainSingleIso {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] [Limits.HasZeroObject A] [Limits.HasZeroObject B]
    (T : A ⥤ B) [T.Additive] :
    (CochainComplex.singleFunctors A).postcomp
        (T.mapHomologicalComplex (ComplexShape.up ℤ)) ≅
      (CochainComplex.singleFunctors B).precomp T :=
  SingleFunctors.isoMk
    (fun n ↦ HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) n)
    (fun k i j h ↦ by
      ext X
      simp only [SingleFunctors.postcomp_shiftIso_hom_app, NatTrans.comp_app,
        Functor.whiskerRight_app, precomp, Iso.trans_hom, Functor.associator_hom_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp]
      rw [Category.assoc,
        T.mapHomologicalComplex_map_singleFunctors_shiftIso_hom_app k i j h X]
      simp only [postcomp_functor, Functor.comp_obj, CochainComplex.shiftFunctor_obj_X',
        Functor.mapHomologicalComplex_obj_X, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplex_commShiftIso_inv_app_f,
        Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
        CochainComplex.shiftFunctor_map_f', Category.id_comp])

/-- Passing the mapped-single comparison to the homotopy category.
(blueprint: lem-pc-pinned-single-tensor-shifts)
-/
def mappedHomotopySingleIso {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] [Limits.HasZeroObject A] [Limits.HasZeroObject B]
    (T : A ⥤ B) [T.Additive] :
    (HomotopyCategory.singleFunctors A).postcomp
        (T.mapHomotopyCategory (ComplexShape.up ℤ)) ≅
      (HomotopyCategory.singleFunctors B).precomp T :=
by
  let F := CochainComplex.singleFunctors A
  let G := CochainComplex.singleFunctors B
  let qA := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let qB := HomotopyCategory.quotient B (ComplexShape.up ℤ)
  let TC := T.mapHomologicalComplex (ComplexShape.up ℤ)
  let TH := T.mapHomotopyCategory (ComplexShape.up ℤ)
  let e₁ : (F.postcomp qA).postcomp TH ≅ F.postcomp (qA ⋙ TH) :=
    F.postcompPostcompIso qA TH
  haveI : NatTrans.CommShift (T.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom ℤ :=
    inferInstance
  haveI : NatTrans.CommShift (T.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  let e₂ : F.postcomp (qA ⋙ TH) ≅ F.postcomp (TC ⋙ qB) :=
    F.postcompIsoOfIso (T.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
  let e₃ : F.postcomp (TC ⋙ qB) ≅ (F.postcomp TC).postcomp qB :=
    (F.postcompPostcompIso TC qB).symm
  let e₄ : (F.postcomp TC).postcomp qB ≅ (G.precomp T).postcomp qB :=
    (SingleFunctors.postcompFunctor A ℤ qB).mapIso (mappedCochainSingleIso T)
  let e₅ : (G.precomp T).postcomp qB ≅ (G.postcomp qB).precomp T :=
    precompPostcompIso G T qB
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅


/-- The homotopy family comparison uses the actual termwise single map.
(blueprint: lem-pc-pinned-single-tensor-shifts)
-/
lemma mappedHomotopySingleIso_hom_app {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] [Limits.HasZeroObject A] [Limits.HasZeroObject B]
    (T : A ⥤ B) [T.Additive] (n : ℤ) (X : A) :
    ((mappedHomotopySingleIso T).hom.hom n).app X =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) n).hom.app X)
        := by
  simp only [postcomp_functor, Functor.comp_obj, Functor.mapHomotopyCategory_obj,
    mappedHomotopySingleIso, postcompPostcompIso, postcompIsoOfIso,
    Functor.mapHomotopyCategoryFactors, mappedCochainSingleIso, precompPostcompIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, comp_hom, isoMk_hom_hom,
    Functor.isoWhiskerLeft_hom, isoMk_inv_hom, postcompFunctor_map_hom,
    NatTrans.comp_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Quotient.lift.isLift_hom,
    Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp]
  all_goals erw [Category.id_comp, Category.comp_id]
  all_goals exact Category.id_comp _

/-- A shift-compatible homotopy counit induces a comparison on derived single families. -/
private theorem exists_single_tensor_shifts_of_counit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (T : A ⥤ B) [T.Additive] (L : DerivedCategory A ⥤ DerivedCategory B)
    [L.CommShift ℤ]
    (ε : DerivedCategory.Qh ⋙ L ⟶
      T.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [NatTrans.CommShift ε ℤ] :
    ∃ τ : (DerivedCategory.singleFunctors A).postcomp L ⟶
        (DerivedCategory.singleFunctors B).precomp T,
      ∀ n G, (τ.hom n).app G =
        cast (by rfl) (ε.app ((HomotopyCategory.singleFunctor A n).obj G) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex T
              (ComplexShape.up ℤ) n).hom.app G))) := by
  let F := HomotopyCategory.singleFunctors A
  let c := (F.postcompPostcompIso DerivedCategory.Qh L).hom ≫
    SingleFunctors.postcompNatTrans F ε ≫
    (F.postcompPostcompIso (T.mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).inv ≫
    SingleFunctors.postcompHom (SingleFunctors.mappedHomotopySingleIso T).hom
      DerivedCategory.Qh ≫
    (SingleFunctors.precompPostcompIso (HomotopyCategory.singleFunctors B) T
      DerivedCategory.Qh).hom
  let e := DerivedCategory.singleFunctorsPostcompQhIso B
  let d : ((HomotopyCategory.singleFunctors B).postcomp DerivedCategory.Qh).precomp T ⟶
      (DerivedCategory.singleFunctors B).precomp T :=
    { hom := fun n ↦ Functor.whiskerLeft T (e.inv.hom n)
      comm := fun k i j h ↦ by
        ext G
        simpa [SingleFunctors.precomp] using congr_app (e.inv.comm k i j h) (T.obj G) }
  refine ⟨SingleFunctors.postcompHom
    (DerivedCategory.singleFunctorsPostcompQhIso A).hom L ≫ c ≫ d, ?_⟩
  intro n G
  change L.map (𝟙 _ ≫ 𝟙 _) ≫
    (𝟙 _ ≫ ε.app ((F.functor n).obj G) ≫
      𝟙 _ ≫ DerivedCategory.Qh.map
        (((SingleFunctors.mappedHomotopySingleIso T).hom.hom n).app G) ≫ 𝟙 _) ≫
      (𝟙 _ ≫ 𝟙 _) = _
  rw [SingleFunctors.mappedHomotopySingleIso_hom_app]
  simp only [Category.id_comp, Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end CategoryTheory.SingleFunctors

namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency.types false

/-- The selected counit followed by the actual termwise mapped-single comparison.
Source: Stacks Project, Tag 08HY; Mathlib mapped-single comparison.
(blueprint: lem-pc-pinned-single-tensor-shifts). -/
def pinnedSingleTensorCounit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (n : ℤ) (G : X.Modules) :
    (derivedPullback.{u, w} g').obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj G) ⟶
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n).obj
        ((Scheme.Modules.tensorPullback g').obj G) :=
  cast (by rfl) ((pinnedPullbackCounit.{u, w} g').app
    ((HomotopyCategory.singleFunctor _ n).obj G) ≫
    DerivedCategory.Qh.{w}.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback g') (ComplexShape.up ℤ) n).hom.app G)))

/-- The tensor comparison is a morphism of single-functor families.
Source: Stacks Project, Tag 08HY; the derived counit universal property and
Mathlib's termwise mapped-single shift identity.
(blueprint: lem-pc-pinned-single-tensor-shifts).
Proof: whisker the pinned left-derived counit by each homotopy single functor,
then compose with Qh applied to the termwise mapped-single comparison. Naturality
follows from the naturality of these two factors. For the shift equation, expand
the single shift using SingleFunctors.postcomp. Apply the counit's
NatTrans.CommShift equation, then the termwise identity
Functor.mapHomologicalComplex_map_singleFunctors_shiftIso_hom_app. Naturality of
the quotient shift comparisons moves them through the mapped-single map.
Functor.map_comp and associativity cancel inverse quotient comparisons. This
proves the Hom.comm equation for every triple k+i=j, including zero and negative
integers, without exactness or flatness of tensor pullback. -/
theorem exists_pinned_single_tensor_shifts
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (s : (derivedPullback.{u, w} g').CommShift ℤ)
    (hs : letI := s; NatTrans.CommShift (pinnedPullbackCounit.{u, w} g') ℤ) :
    letI := s
    ∃ τ : (DerivedCategory.singleFunctors
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))).postcomp
          (derivedPullback.{u, w} g') ⟶
      (DerivedCategory.singleFunctors
        (SheafOfModules.{u} (moduleRings X'.toRingedSpace))).precomp
          (Scheme.Modules.tensorPullback g'),
      ∀ n G, (τ.hom n).app G = pinnedSingleTensorCounit.{u, w} g' n G := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let := s
  have := hs
  exact SingleFunctors.exists_single_tensor_shifts_of_counit
    (A := SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (B := SheafOfModules.{u} (moduleRings X'.toRingedSpace))
    (Scheme.Modules.tensorPullback g') (derivedPullback g') (pinnedPullbackCounit g')

end AlgebraicGeometry
