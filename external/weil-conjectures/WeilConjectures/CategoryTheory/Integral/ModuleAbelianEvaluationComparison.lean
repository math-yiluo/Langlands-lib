/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.RingedSiteModules

import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.RightDerivedExactComposite
import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Module and abelian evaluation cohomology on a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 03FD, second displayed equality
(blueprint: lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem forgotten_injective_evaluation_acyclic
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{u}) (U : C) (I : SheafOfModules.{u} R) [Injective I] :
    (sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightAcyclic
        ((SheafOfModules.toSheaf R).obj I) := by
  let : EnoughInjectives (Sheaf J AddCommGrpCat.{u}) :=
    @IsGrothendieckAbelian.enoughInjectives _ _ _
      (Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} J AddCommGrpCat.{u})
  let : HasExt.{u} (Sheaf J AddCommGrpCat.{u}) := hasExt_of_enoughInjectives _
  intro n
  let : Subsingleton (Sheaf.H' ((SheafOfModules.toSheaf R).obj I) (n + 1) U) :=
    injective_module_abelian_acyclic U I (n + 1) (Nat.succ_pos n)
  obtain ⟨d⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived J U (n + 1)
  have hz : IsZero (Sheaf.H' ((SheafOfModules.toSheaf R).obj I) (n + 1) U) :=
    AddCommGrpCat.isZero_of_subsingleton _
  exact hz.of_iso (d.app ((SheafOfModules.toSheaf R).obj I)).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- An exact functor sending injectives to acyclic objects commutes with right derivation.
The components are computed from the mapped injective resolutions. -/
noncomputable def exact_comp_comparison
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [EnoughInjectives A] [EnoughInjectives B]
    (T : A ⥤ B) (F : B ⥤ D) [T.Additive] [F.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] [PreservesFiniteLimits F]
    (hT : ∀ (I : A) [Injective I], F.rightAcyclic (T.obj I)) (q : ℕ) :
    (T ⋙ F).rightDerived q ≅ T ⋙ F.rightDerived q :=
  NatIso.ofComponents (fun M ↦
    (injectiveResolution M).isoRightDerivedObj (T ⋙ F) q ≪≫
      (F.rightDerivedObjIsoOfResolution (T.mapResolution (injectiveResolution M).ι)
        (fun n ↦ hT ((injectiveResolution M).cocomplex.X n)) q).symm) (by
    intro M N f
    let I := injectiveResolution M
    let K := injectiveResolution N
    let φ := InjectiveResolution.desc f K I
    let ι := T.mapResolution I.ι
    let κ := T.mapResolution K.ι
    let c := F.rightDerivedObjIsoOfResolution ι (fun n ↦ hT (I.cocomplex.X n)) q
    let d := F.rightDerivedObjIsoOfResolution κ (fun n ↦ hT (K.cocomplex.X n)) q
    have hw : ι ≫ (T.mapHomologicalComplex _).map φ =
        (CochainComplex.single₀ _).map (T.map f) ≫ κ := by
      dsimp only [ι, κ, Functor.mapResolution]
      rw [Category.assoc, ← Functor.map_comp, InjectiveResolution.desc_commutes,
        Functor.map_comp, ← Category.assoc]
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun k ↦ k ≫ (T.mapHomologicalComplex _).map K.ι)
          ((HomologicalComplex.singleMapHomologicalComplex T
            (ComplexShape.up ℕ) 0).inv.naturality f).symm
    have hc := acyclicComparison_naturality F ι κ
      (fun n ↦ hT (I.cocomplex.X n)) (fun n ↦ hT (K.cocomplex.X n))
      (T.map f) ((T.mapHomologicalComplex _).map φ) hw q
    have hd := InjectiveResolution.isoRightDerivedObj_hom_naturality f I K φ
      (InjectiveResolution.desc_commutes_zero f K I) (T ⋙ F) q
    change ((T ⋙ F).rightDerived q).map f ≫
        ((K.isoRightDerivedObj (T ⋙ F) q).hom ≫ d.inv) =
      ((I.isoRightDerivedObj (T ⋙ F) q).hom ≫ c.inv) ≫ (F.rightDerived q).map (T.map f)
    rw [← Category.assoc, hd, Category.assoc]
    simp only [Category.assoc]
    convert congrArg (fun k ↦ (I.isoRightDerivedObj (T ⋙ F) q).hom ≫ k) hc using 1
    rfl)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The exact-composite comparison is computed by every compatible resolution lift. -/
theorem exact_comp_comparison_formula
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [EnoughInjectives A] [EnoughInjectives B]
    (T : A ⥤ B) (F : B ⥤ D) [T.Additive] [F.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] [PreservesFiniteLimits F]
    (hT : ∀ (I : A) [Injective I], F.rightAcyclic (T.obj I))
    (M : A) (I : InjectiveResolution M) (K : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K.cocomplex)
    (hφ : T.map (I.ι.f 0) ≫ φ.f 0 = K.ι.f 0) (q : ℕ) :
    (exact_comp_comparison T F hT q).hom.app M ≫ (K.isoRightDerivedObj F q).hom =
      (I.isoRightDerivedObj (T ⋙ F) q).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) q := by
  have hcomp (L : CochainComplex A ℕ) :
      (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ F)) (.up ℕ)).inv.app L =
        𝟙 _ := by
    ext n
    rfl
  obtain ⟨a, ha⟩ := Functor.exists_rightDerived_exact_comp_iso T F
    (fun I hI ↦ @hT I hI) M q
  let I₀ := injectiveResolution M
  let K₀ := injectiveResolution (T.obj M)
  let φ₀ := InjectiveResolution.descOfQuasiIso (𝟙 (T.obj M)) K₀ (T.mapResolution I₀.ι)
  have hφ₀ : T.map (I₀.ι.f 0) ≫ φ₀.f 0 = K₀.ι.f 0 := by
    have h := InjectiveResolution.descOfQuasiIso_commutes
      (𝟙 (T.obj M)) K₀ (T.mapResolution I₀.ι)
    simpa [φ₀, Functor.mapResolution] using congrArg (fun f ↦ f.f 0) h
  have hcanonical : (exact_comp_comparison T F hT q).hom.app M = a.hom := by
    rw [ha I₀ K₀ φ₀ hφ₀, hcomp, HomologicalComplex.homologyMap_id]
    erw [Category.id_comp]
    change (I₀.isoRightDerivedObj (T ⋙ F) q).hom ≫
        (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ₀) q ≫
          (K₀.isoRightDerivedObj F q).inv) = _
    rfl
  rw [hcanonical, ha I K φ hφ, hcomp, HomologicalComplex.homologyMap_id]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The exact-composite comparison preserves the canonical degree-zero augmentation. -/
theorem exact_comp_comparison_zero
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [EnoughInjectives A] [EnoughInjectives B]
    (T : A ⥤ B) (F : B ⥤ D) [T.Additive] [F.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] [PreservesFiniteLimits F]
    (hT : ∀ (I : A) [Injective I], F.rightAcyclic (T.obj I)) :
    (T ⋙ F).toRightDerivedZero ≫ (exact_comp_comparison T F hT 0).hom =
      Functor.whiskerLeft T F.toRightDerivedZero := by
  ext M
  let I := injectiveResolution M
  let K := injectiveResolution (T.obj M)
  let φ := InjectiveResolution.descOfQuasiIso (𝟙 (T.obj M)) K (T.mapResolution I.ι)
  have hφ : T.map (I.ι.f 0) ≫ φ.f 0 = K.ι.f 0 := by
    have h := InjectiveResolution.descOfQuasiIso_commutes
      (𝟙 (T.obj M)) K (T.mapResolution I.ι)
    simpa [φ, Functor.mapResolution] using congrArg (fun f ↦ f.f 0) h
  let ψ := (F.mapHomologicalComplex (.up ℕ)).map φ
  have hcycles : I.toRightDerivedZero' (T ⋙ F) ≫
      HomologicalComplex.cyclesMap ψ 0 = K.toRightDerivedZero' F := by
    apply (cancel_mono (HomologicalComplex.iCycles _ 0)).1
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    erw [InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    change F.map (T.map (I.ι.f 0)) ≫ F.map (φ.f 0) = F.map (K.ι.f 0)
    rw [← F.map_comp, hφ]
  change (T ⋙ F).toRightDerivedZero.app M ≫
    (exact_comp_comparison T F hT 0).hom.app M = F.toRightDerivedZero.app (T.obj M)
  apply (cancel_mono (K.isoRightDerivedObj F 0).hom).1
  rw [Category.assoc, exact_comp_comparison_formula T F hT M I K φ hφ 0,
    I.toRightDerivedZero_eq (T ⋙ F), K.toRightDerivedZero_eq F]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change I.toRightDerivedZero' (T ⋙ F) ≫
      (((T ⋙ F).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ 0 ≫
        HomologicalComplex.homologyMap ψ 0 =
    K.toRightDerivedZero' F ≫
      ((F.mapHomologicalComplex (.up ℕ)).obj K.cocomplex).homologyπ 0
  erw [HomologicalComplex.homologyπ_naturality ψ 0]
  rw [← Category.assoc, hcycles]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The right derived evaluation of module sheaves agrees naturally with the right
 derived evaluation of their underlying abelian sheaves. The equation in degree zero
 identifies the two augmentations from sections, so the comparison is the identity
 on sections under the canonical degree-zero identifications. The final clause characterizes
 the canonical map by every lift from a module resolution to an abelian resolution.

Source: Stacks Project, Cohomology on Sites, Tag 03FD, objectwise equality
(blueprint: lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison).

Proof: Forgetting module structure is exact by moduleSheaves_colimits_forgetful.
The existing general-site theorem injective_module_abelian_acyclic gives positive
abelian cohomology vanishing on forgotten injective module sheaves. The comparison
between object cohomology and right derived evaluation turns this into evaluation
acyclicity. Thus a forgotten injective module resolution computes abelian derived
evaluation as well as module derived evaluation. Compose the two resolution
isomorphisms. Their naturality for one lift of each module morphism assembles the
components into natural isomorphisms. The canonical exact-composite comparison
identifies their maps with the homology maps of every augmentation-compatible lift.
In degree zero, the augmentation equation gives equality after the cycle inclusion;
naturality of the homology projection and toRightDerivedZero_eq then prove the
specified normalization. No injectivity after forgetting or coefficient flatness is used. -/
theorem module_abelian_evaluation_comparison_general
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{u})
    [EnoughInjectives (ringedSiteModules.{u} R)] (U : C) :
    ∃! e : ∀ q : ℕ,
      (SheafOfModules.toSheaf R ⋙
        (sheafToPresheaf J AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).rightDerived q ≅
      SheafOfModules.toSheaf R ⋙
        (sheafToPresheaf J AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q,
      ((SheafOfModules.toSheaf R ⋙
        (sheafToPresheaf J AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).toRightDerivedZero ≫
          (e 0).hom =
        Functor.whiskerLeft (SheafOfModules.toSheaf R)
          ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).toRightDerivedZero)) ∧
      ∀ (M : ringedSiteModules.{u} R) (I : InjectiveResolution M)
        (K : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
        (φ : ((SheafOfModules.toSheaf R).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
          K.cocomplex)
        (_hφ : (SheafOfModules.toSheaf R).map (I.ι.f 0) ≫ φ.f 0 = K.ι.f 0) (q : ℕ),
        (e q).hom.app M ≫
            (K.isoRightDerivedObj
              (sheafToPresheaf J AddCommGrpCat.{u} ⋙
                (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).hom =
          (I.isoRightDerivedObj
            (SheafOfModules.toSheaf R ⋙
              (sheafToPresheaf J AddCommGrpCat.{u} ⋙
                (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))) q).hom ≫
            HomologicalComplex.homologyMap
              (((sheafToPresheaf J AddCommGrpCat.{u} ⋙
                (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
                  (.up ℕ)).map φ) q := by
  let T := SheafOfModules.toSheaf R
  let : PreservesFiniteColimits T := (moduleSheaves_colimits_forgetful R).2.2.1
  let F := sheafToPresheaf J AddCommGrpCat.{u} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)
  have hT (I : ringedSiteModules.{u} R) [Injective I] :
      F.rightAcyclic (T.obj I) := forgotten_injective_evaluation_acyclic J R U I
  refine ⟨fun q ↦ exact_comp_comparison T F hT q, ?_, ?_⟩
  · refine ⟨exact_comp_comparison_zero T F hT, ?_⟩
    intro M I K φ hφ q
    exact exact_comp_comparison_formula T F hT M I K φ hφ q
  · intro e he
    -- A single compatible lift determines each component after cancelling its target iso.
    funext q
    apply Iso.ext
    apply NatTrans.ext
    funext M
    let I := injectiveResolution M
    let K := injectiveResolution (T.obj M)
    let φ := InjectiveResolution.descOfQuasiIso (𝟙 (T.obj M)) K (T.mapResolution I.ι)
    have hφ : T.map (I.ι.f 0) ≫ φ.f 0 = K.ι.f 0 := by
      have h := InjectiveResolution.descOfQuasiIso_commutes
        (𝟙 (T.obj M)) K (T.mapResolution I.ι)
      simpa [φ, Functor.mapResolution] using congrArg (fun f ↦ f.f 0) h
    apply (cancel_mono (K.isoRightDerivedObj F q).hom).1
    exact (he.2 M I K φ hφ q).trans
      (exact_comp_comparison_formula T F hT M I K φ hφ q).symm

end CategoryTheory
