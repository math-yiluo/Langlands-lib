/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Constant.ConstantLeftModuleTransportSupplement
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange

import WeilConjectures.CategoryTheory.RightDerivedPlusCube
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
public import WeilConjectures.CategoryTheory.Constant.ConstantLeftModuleInverseImageCoherence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Derived evaluation and forgetting constant left-module scalars

Source: Stacks Project, sites-cohomology.tex, Tag 03FD, and derived.tex, Tags 05TA and 015E
(blueprint: lem-pe-left-module-derived-evaluation-forget).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace CategoryTheory.LeftModuleDerivedEvaluation

open ConstantLeftModuleInverseImage

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]

/-- Restrict the sectionwise action along the constant-ring sheafification unit.
Source: Stacks, 03FD (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
abbrev constantPresheafModules : Modules J Λ ⥤
    PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) :=
  SheafOfModules.forget ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) ⋙
    PresheafOfModules.restrictScalars
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))

/-- Evaluation with its constant left `Λ`-action, including for noncommutative `Λ`.
Source: Stacks, 03FD (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
abbrev G (W : C) : Modules J Λ ⥤ ModuleCat.{u} Λ :=
  constantPresheafModules J Λ ⋙
    PresheafOfModules.evaluation ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) (op W)

/-- Evaluation on abelian sheaves.
Source: Stacks, 01FT/03FD (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
abbrev G₀ (W : C) : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections J AddCommGrpCat.{u}).obj (op W)

/-- The scalar-forgetting functor on left modules.
Source: Stacks, 03FD (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
abbrev v : ModuleCat.{u} Λ ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}

/-- The literal identity between the two underlying abelian evaluation functors.
Source: Stacks, 03FD, first proof paragraph
(blueprint: lem-pe-left-module-derived-evaluation-forget). -/
def evaluationIdentity (W : C) : G J Λ W ⋙ v Λ ≅ V J Λ ⋙ G₀ J W :=
  Iso.refl _

/-- Restriction of evaluated left-module sections along an arrow in the site.
Source: Stacks, 03FD (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
def restriction {W W' : C} (f : W' ⟶ W) : G J Λ W ⟶ G J Λ W' :=
  Functor.whiskerLeft (constantPresheafModules J Λ)
    (PresheafOfModules.restriction ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) f.op ≫
      Functor.whiskerLeft
        (PresheafOfModules.evaluation ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) (op W'))
        (ModuleCat.restrictScalarsId' (RingHom.id Λ) rfl).hom)

/-- Restriction of evaluated abelian sections along the same site arrow.
Source: Stacks, 03FD (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
abbrev restriction₀ {W W' : C} (f : W' ⟶ W) : G₀ J W ⟶ G₀ J W' :=
  (sheafSections J AddCommGrpCat.{u}).map f.op

/-- Additivity inherited from Mathlib's presheaf scalar restriction and evaluation.
Source: Stacks, 03FD (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
instance gAdditive (W : C) : (G J Λ W).Additive :=
  inferInstanceAs ((constantPresheafModules J Λ ⋙
    PresheafOfModules.evaluation ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) (op W)).Additive)

/-- Additivity inherited from the underlying presheaf evaluation.
Source: Stacks, 01FT (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
instance g₀Additive (W : C) : (G₀ J W).Additive :=
  inferInstanceAs ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)).Additive)

/-- Exactness of scalar forgetting, from the recorded colimit theorem.
Source: Stacks, 03DA/03DB (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
instance vPreservesFiniteColimits : PreservesFiniteColimits (V J Λ) :=
  (moduleSheaves_colimits_forgetful
    ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))).2.2.1

variable [HasDerivedCategory.{w} (Modules J Λ)]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u})]
  [HasDerivedCategory.{w} (ModuleCat.{u} Λ)] [HasDerivedCategory.{w} AddCommGrpCat.{u}]
  [EnoughInjectives (Modules J Λ)] [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]

/-- The canonical derived square comparison, obtained from the underived identity.
Source: Stacks, 03FD/05TA (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
def comparison (W : C) :
    (G J Λ W).rightDerivedFunctorPlus ⋙ (v Λ).mapDerivedCategoryPlus ⟶
      (V J Λ).mapDerivedCategoryPlus ⋙ (G₀ J W).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (evaluationIdentity J Λ W).hom

/-- Pull a section back as a map from the terminal constant sheaf. This is the
geometric adjunction's global-cohomology map before derivation.
Source: Stacks, 00YV/0736 (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
def pullbackSection {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    (p : L.obj ((constantSheaf J (Type u)).obj PUnit.{u + 1}) ≅
      (constantSheaf K (Type u)).obj PUnit.{u + 1})
    {T : C} (hT : IsTerminal T) {S : D} (hS : IsTerminal S)
    (F : Sheaf J (Type u)) (x : F.obj.obj (op T)) : (L.obj F).obj.obj (op S) :=
  ((constantSheafAdj K (Type u) hS).homEquiv _ _
    (p.inv ≫ L.map ((constantSheafAdj J (Type u) hT).homEquiv _ _ |>.symm
      (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ x))))) PUnit.unit

end CategoryTheory.LeftModuleDerivedEvaluation

namespace CategoryTheory.LeftModuleDerivedEvaluation

open ConstantLeftModuleInverseImage

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {Λ : Type u} [Ring Λ] [HasWeakSheafify J RingCat.{u}]
  [HasWeakSheafify K RingCat.{u}]
  {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
  {R : Sheaf K (Type u) ⥤ Sheaf J (Type u)}
  {adj : L ⊣ R} {hL : PreservesFiniteLimits L}

/-- The canonical global pullback maps, normalized on sections using the geometric
inverse image and its underlying-set comparisons. The normalization determines each
component on every element, so the maps are unique.
Source: Stacks, 00YV/0736 (blueprint: lem-pe-left-module-derived-evaluation-forget). -/
structure GlobalPullback
    (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL)
    {T : C} (hT : IsTerminal T) {S : D} (hS : IsTerminal S) where
  moduleMap : G J Λ T ⟶ d.moduleFunctor ⋙ G K Λ S
  abelianMap : G₀ J T ⟶ d.abelianInverse ⋙ G₀ K S
  module_normalization : ∀ (M : Modules J Λ) (x : (G J Λ T).obj M),
    moduleMap.app M x =
      (d.moduleSetIso.inv.app M).hom.app (op S)
        (pullbackSection J K d.pointIso hT hS ((W J Λ).obj M) x)
  abelian_normalization : ∀ (A : Sheaf J AddCommGrpCat.{u}) (x : (G₀ J T).obj A),
    abelianMap.app A x =
      (d.abelianSetIso.inv.app A).hom.app (op S)
        (pullbackSection J K d.pointIso hT hS ((U J).obj A) x)

variable [HasDerivedCategory.{w} (Modules J Λ)]
  [HasDerivedCategory.{w} (Modules K Λ)]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u})]
  [HasDerivedCategory.{w} (Sheaf K AddCommGrpCat.{u})]
  [HasDerivedCategory.{w} (ModuleCat.{u} Λ)] [HasDerivedCategory.{w} AddCommGrpCat.{u}]
  [EnoughInjectives (Modules J Λ)] [EnoughInjectives (Modules K Λ)]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{u})]

end CategoryTheory.LeftModuleDerivedEvaluation

namespace CategoryTheory
open ConstantLeftModuleInverseImage LeftModuleDerivedEvaluation
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derivedNatIso_refl (Λ : Type u) [Ring Λ]
    [HasDerivedCategory.{w} (ModuleCat.{u} Λ)] [HasDerivedCategory.{w} AddCommGrpCat.{u}] :
    Functor.mapDerivedCategoryPlusNatIso (Iso.refl (v Λ)) =
      Iso.refl (v Λ).mapDerivedCategoryPlus := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (ModuleCat.{u} Λ))
  intro M
  apply (cancel_mono ((v Λ).mapDerivedCategoryPlusFactorsh.hom.app M)).mp
  rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  simp only [Iso.refl_hom, NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app,
    Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

section Sections
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    (p : L.obj ((constantSheaf J (Type u)).obj PUnit.{u + 1}) ≅
      (constantSheaf K (Type u)).obj PUnit.{u + 1})
    {T : C} {S : D} (hT : IsTerminal T) (hS : IsTerminal S)

private noncomputable def pointMap (F : Sheaf J (Type u)) (x : F.obj.obj (op T)) :
    (constantSheaf J (Type u)).obj PUnit.{u + 1} ⟶ F :=
  ((constantSheafAdj J (Type u) hT).homEquiv _ _).symm
    (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ x))

end Sections

section Normalized
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {R : Sheaf K (Type u) ⥤ Sheaf J (Type u)}
    {adj : L ⊣ R} {hL : PreservesFiniteLimits L}
    (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL)
    {T : C} {S : D} (hT : IsTerminal T) (hS : IsTerminal S)

private noncomputable def abelianSection (A : Sheaf J AddCommGrpCat.{u})
    (x : A.obj.obj (op T)) : (d.abelianInverse.obj A).obj.obj (op S) :=
  (d.abelianSetIso.inv.app A).hom.app (op S)
    (pullbackSection J K d.pointIso hT hS ((U J).obj A) x)

private noncomputable def scalarMap (M : Modules J Λ) (r : Λ) :
    (V J Λ).obj M ⟶ (V J Λ).obj M :=
  ⟨{ app := fun Q ↦ AddCommGrpCat.ofHom
        (DistribSMul.toAddMonoidHom (M.val.obj Q)
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app Q r))
     naturality := by
       intro Q Q' f
       ext x
       have hm := M.val.map_smul f
         ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app Q r)
         (show M.val.obj Q from x)
       have hr := congrArg (fun k ↦ k r)
         ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).naturality f)
       have hh := congrArg (fun t : ((constantSheaf J RingCat.{u}).obj
         (RingCat.of Λ)).obj.obj Q' ↦ t • (M.val.map f x : M.val.obj Q')) hr
       exact hh.trans hm.symm }⟩

private noncomputable def moduleSection (M : Modules J Λ)
    (x : (G J Λ T).obj M) : (G K Λ S).obj (d.moduleFunctor.obj M) :=
  (d.underlyingIso.inv.app M).hom.app (op S)
    (abelianSection J K Λ d hT hS ((V J Λ).obj M) x)

end Normalized

section Derived
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    [HasDerivedCategory.{w} (Modules J Λ)] [HasDerivedCategory.{w} (Modules K Λ)]
    [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u})]
    [HasDerivedCategory.{w} (Sheaf K AddCommGrpCat.{u})]
    [HasDerivedCategory.{w} (ModuleCat.{u} Λ)] [HasDerivedCategory.{w} AddCommGrpCat.{u}]
    [EnoughInjectives (Modules J Λ)] [EnoughInjectives (Modules K Λ)]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
    [EnoughInjectives (Sheaf K AddCommGrpCat.{u})]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {R : Sheaf K (Type u) ⥤ Sheaf J (Type u)}
    {adj : L ⊣ R} {hL : PreservesFiniteLimits L}
    (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL)
    {T : C} {S : D} (hT : IsTerminal T) (hS : IsTerminal S)
    (b : GlobalPullback d hT hS)

end Derived

end CategoryTheory

namespace CategoryTheory.LeftModuleDerivedEvaluation
open ConstantLeftModuleInverseImage

end CategoryTheory.LeftModuleDerivedEvaluation

namespace CategoryTheory

open ConstantLeftModuleInverseImage LeftModuleDerivedEvaluation

end CategoryTheory
