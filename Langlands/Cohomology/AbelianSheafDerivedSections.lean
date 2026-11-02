import Langlands.Cohomology.ExtRightDerived
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.Abelian

/-! # Actual abelian-sheaf cohomology as right-derived global sections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Langlands.Cohomology.AbelianSheafDerivedSections

variable (X : TopCat.{u})

/-- The actual constant integer sheaf used to define Mathlib's sheaf cohomology. -/
abbrev constantIntegers : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))

/-- Global sections of an actual abelian sheaf. -/
abbrev globalSections : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)

instance : (globalSections X).Additive where

instance : (globalSections X).IsRightAdjoint :=
  (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    (isTerminalTop (α := Opens X))).isRightAdjoint

instance : PreservesFiniteLimits (globalSections X) :=
  inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Hom from the actual constant integer sheaf is naturally global sections. -/
def homGlobalSectionsIso :
    preadditiveCoyoneda.obj (op (constantIntegers X)) ≅ globalSections X :=
  NatIso.ofComponents
    (fun F => (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        (isTerminalTop (α := Opens X))).homAddEquiv _ F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)).toAddCommGrpIso)
    (fun {F G} f => by
      ext g
      have h := (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        (isTerminalTop (α := Opens X))).homEquiv_naturality_right g f
      exact congrArg (AddCommGrpCat.uliftZMultiplesAddEquiv _) h)

/-- The right-derived Hom/global-sections comparison. -/
def homRightDerivedIso (n : ℕ) :
    (preadditiveCoyoneda.obj (op (constantIntegers X))).rightDerived n ≅
      (globalSections X).rightDerived n where
  hom := NatTrans.rightDerived (homGlobalSectionsIso X).hom n
  inv := NatTrans.rightDerived (homGlobalSectionsIso X).inv n
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id, NatTrans.rightDerived_id]

set_option backward.isDefEq.respectTransparency false in
/-- Mathlib's actual Ext-defined cohomology agrees additively with right-derived
global sections, in every nonnegative degree. -/
def HAddEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Sheaf.H.{u} F n ≃+ ((globalSections X).rightDerived n).obj F :=
  (ExtRightDerived.extAddEquivRightDerived (constantIntegers X) F n).trans
    ((homRightDerivedIso X n).app F).addCommGroupIsoToAddEquiv

end Langlands.Cohomology.AbelianSheafDerivedSections
