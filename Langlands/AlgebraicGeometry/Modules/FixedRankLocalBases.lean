import Langlands.AlgebraicGeometry.LocallyFreeRank
import Mathlib.CategoryTheory.Sites.Spaces

/-! # Fixed rank from free charts -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace Langlands.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A free chart for the restriction gives a free chart on the corresponding slice site. -/
def freeOverIsoOfRestrict (M : X.Modules) (U : X.Opens) (I : Type u)
    (e : M.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U :=
  SheafOfModules.mapFreeIso (overEquiv U).inverse I
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm ≪≫
    (overEquiv U).inverse.mapIso e.symm ≪≫
    (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M).symm ≪≫
    ((overEquiv U).unitIso.app (M.over U)).symm

/-- Local generators supplied by a neighborhood of each point with a specified free chart. -/
def freeNeighborhoodGenerators (M : X.Modules) (U : X → X.Opens)
    (hx : ∀ x, x ∈ U x) (I : X → Type u)
    (e : ∀ x, M.restrict (U x).ι ≅
      SheafOfModules.free (R := (U x).toScheme.ringCatSheaf) (I x)) :
    SheafOfModules.LocalGeneratorsData.{u} M where
  I := X
  X := U
  coversTop := (_root_.Opens.coversTop_iff X U).mpr (by
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩)
  generators x := (SheafOfModules.free.generatingSections (I x)).ofEpi
    (freeOverIsoOfRestrict M (U x) (I x) (e x)).hom

/-- The chosen generators are local bases. -/
lemma freeNeighborhoodGenerators_isLocallyFreeData (M : X.Modules) (U : X → X.Opens)
    (hx : ∀ x, x ∈ U x) (I : X → Type u)
    (e : ∀ x, M.restrict (U x).ι ≅
      SheafOfModules.free (R := (U x).toScheme.ringCatSheaf) (I x)) :
    (freeNeighborhoodGenerators M U hx I e).IsLocallyFreeData where
  isIso x := by
    change IsIso ((SheafOfModules.free.generatingSections (I x)).ofEpi
      (freeOverIsoOfRestrict M (U x) (I x) (e x)).hom).π
    rw [SheafOfModules.GeneratingSections.ofEpi_π]
    infer_instance

/-- Free neighborhoods with exactly `n` generators give the actual fixed-rank condition. -/
theorem isLocallyFreeOfRank_of_freeNeighborhoods (M : X.Modules) (n : ℕ)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Nonempty (M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin n)))) :
    IsLocallyFreeOfRank M n := by
  classical
  choose U hx e using h
  refine ⟨freeNeighborhoodGenerators M U hx (fun _ => ULift.{u} (Fin n))
      (fun x => (e x).some),
    freeNeighborhoodGenerators_isLocallyFreeData M U hx (fun _ => ULift.{u} (Fin n))
      (fun x => (e x).some), ?_⟩
  intro x
  exact ⟨Equiv.ulift⟩

end Langlands.Scheme.Modules
