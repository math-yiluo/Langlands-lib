import Langlands.Sheaf.Renard.RingedBasisModules
import Langlands.Sheaf.Renard.GermSectionSheaf

/-!
# Intrinsic module-sheaf gluing and the all-open specialization

Gluing retains the original section modules and every member of an arbitrarily
sized indexed cover. The all-open category instantiates the same construction.
-/

open CategoryTheory Opposite TopologicalSpace

universe u r v w

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

namespace BasisModuleSheaf

variable {S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r}}

@[simp]
theorem restrict_self (M : BasisModuleSheaf.{u,r,v} S)
    (U : BasisOpen B) (m : M.sections U) :
    M.restrict (U := U) le_rfl m = m :=
  restriction_self_apply M.obj.presheaf U m

theorem restrict_comp (M : BasisModuleSheaf.{u,r,v} S)
    {U V W : BasisOpen B} (hUV : U.obj ≤ V.obj) (hVW : V.obj ≤ W.obj)
    (m : M.sections W) :
    M.restrict hUV (M.restrict hVW m) = M.restrict (hUV.trans hVW) m :=
  restriction_comp_apply M.obj.presheaf hUV hVW m

/-- Actual unique gluing on all original cover members, with an independent index universe. -/
theorem unique_gluing (M : BasisModuleSheaf.{u,r,v} S) {ι : Type w}
    (V : BasisOpen B) (U : ι → BasisOpen B) (hU : FamilyCovers V U)
    (s : ∀ i, M.sections (U i))
    (hs : ∀ i j (W : BasisOpen B) (hWi : W.obj ≤ (U i).obj)
      (hWj : W.obj ≤ (U j).obj), M.restrict hWi (s i) = M.restrict hWj (s j)) :
    ∃! t : M.sections V, ∀ i, M.restrict (hU.1 i) t = s i :=
  SheafCondition.family M.obj.presheaf M.property ι V U hU s hs

/-- Agreement on a covering family determines an original module section. -/
theorem sections_ext (M : BasisModuleSheaf.{u,r,v} S) {ι : Type w}
    {V : BasisOpen B} {U : ι → BasisOpen B} (hU : FamilyCovers V U)
    {s t : M.sections V} (h : ∀ i, M.restrict (hU.1 i) s = M.restrict (hU.1 i) t) :
    s = t := by
  have hc : ∀ i j (W : BasisOpen B) (hWi : W.obj ≤ (U i).obj)
      (hWj : W.obj ≤ (U j).obj),
      M.restrict hWi (M.restrict (hU.1 i) t) =
        M.restrict hWj (M.restrict (hU.1 j) t) := by
    intro i j W hWi hWj
    rw [M.restrict_comp, M.restrict_comp]
  obtain ⟨a, _, ha⟩ := M.unique_gluing V U hU (fun i => M.restrict (hU.1 i) t) hc
  exact (ha s h).trans (ha t (fun _ => rfl)).symm

end BasisModuleSheaf

/-- The same actual module-sheaf category on the published basis of all opens. -/
abbrev AllOpenModuleSheaf
    (S : (BasisOpen (allOpenBasis X))ᵒᵖ ⥤ RingCat.{r}) :=
  BasisModuleSheaf.{u,r,v} S

namespace AllOpenModuleSheaf

variable {S : (BasisOpen (allOpenBasis X))ᵒᵖ ⥤ RingCat.{r}}

/-- Sections on an actual open are the original module-presheaf value. -/
abbrev sections (M : AllOpenModuleSheaf.{u,r,v} S) (U : Opens X) :
    ModuleCat.{v} (S.obj (op (allOpen U))) :=
  BasisModuleSheaf.sections M (allOpen U)

/-- Restriction along an actual inclusion is the same semilinear restriction. -/
noncomputable def restrict (M : AllOpenModuleSheaf.{u,r,v} S)
    {U V : Opens X} (h : U ≤ V) :
    sections M V →ₛₗ[(ringRestriction S (U := allOpen U) (V := allOpen V) h).hom]
      sections M U :=
  BasisModuleSheaf.restrict M h

@[simp]
theorem sections_eq (M : AllOpenModuleSheaf.{u,r,v} S) (U : Opens X) :
    sections M U = M.obj.obj (op (allOpen U)) := rfl

@[simp]
theorem restrict_apply (M : AllOpenModuleSheaf.{u,r,v} S)
    {U V : Opens X} (h : U ≤ V) (m : sections M V) :
    restrict M h m = M.obj.map (basisHom (U := allOpen U) (V := allOpen V) h).op m := rfl

theorem restrict_smul (M : AllOpenModuleSheaf.{u,r,v} S)
    {U V : Opens X} (h : U ≤ V) (a : S.obj (op (allOpen V))) (m : sections M V) :
    restrict M h (a • m) =
      ringRestriction S (U := allOpen U) (V := allOpen V) h a • restrict M h m :=
  BasisModuleSheaf.restrict_smul M h a m

/-- Linear components on actual opens keep the original morphism values. -/
abbrev app {M N : AllOpenModuleSheaf.{u,r,v} S} (f : M ⟶ N) (U : Opens X) :
    sections M U ⟶ sections N U :=
  BasisModuleSheaf.app f (allOpen U)

@[simp]
theorem app_apply {M N : AllOpenModuleSheaf.{u,r,v} S} (f : M ⟶ N)
    (U : Opens X) (m : sections M U) :
    app f U m = f.hom.app (op (allOpen U)) m := rfl

/-- All-open gluing is the same basis gluing, with no bound on the index type. -/
theorem unique_gluing (M : AllOpenModuleSheaf.{u,r,v} S) {ι : Type w}
    (V : Opens X) (U : ι → Opens X)
    (hU : (∀ i, U i ≤ V) ∧ ∀ x ∈ V, ∃ i, x ∈ U i)
    (s : ∀ i, sections M (U i))
    (hs : ∀ i j (W : Opens X) (hWi : W ≤ U i) (hWj : W ≤ U j),
      restrict M hWi (s i) = restrict M hWj (s j)) :
    ∃! t : sections M V, ∀ i, restrict M (hU.1 i) t = s i := by
  apply BasisModuleSheaf.unique_gluing M (allOpen V) (fun i => allOpen (U i)) hU s
  intro i j W hWi hWj
  exact hs i j W.obj hWi hWj

end AllOpenModuleSheaf

/-- Evaluation on an actual open instantiates the existing module-sheaf evaluation. -/
def allOpenModuleSheafEvaluation
    (S : (BasisOpen (allOpenBasis X))ᵒᵖ ⥤ RingCat.{r}) (U : Opens X) :
    AllOpenModuleSheaf.{u,r,v} S ⥤ ModuleCat.{v} (S.obj (op (allOpen U))) :=
  moduleSheafEvaluation S (allOpen U)

@[simp]
theorem allOpenModuleSheafEvaluation_obj
    (S : (BasisOpen (allOpenBasis X))ᵒᵖ ⥤ RingCat.{r})
    (U : Opens X) (M : AllOpenModuleSheaf.{u,r,v} S) :
    (allOpenModuleSheafEvaluation S U).obj M = AllOpenModuleSheaf.sections M U := rfl

@[simp]
theorem allOpenModuleSheafEvaluation_map
    (S : (BasisOpen (allOpenBasis X))ᵒᵖ ⥤ RingCat.{r})
    (U : Opens X) {M N : AllOpenModuleSheaf.{u,r,v} S} (f : M ⟶ N) :
    (allOpenModuleSheafEvaluation S U).map f = AllOpenModuleSheaf.app f U := rfl

end Langlands.Sheaf.Renard
