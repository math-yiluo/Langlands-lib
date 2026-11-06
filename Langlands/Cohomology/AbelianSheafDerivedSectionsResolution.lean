import Langlands.Cohomology.ExtAdjunctionResolution
import Langlands.Cohomology.AbelianSheafDerivedSections

/-! # Actual sheaf cohomology on any injective resolution -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Langlands.Cohomology.AbelianSheafDerivedSections

variable (X : TopCat.{u}) {F : TopCat.Sheaf AddCommGrpCat.{u} X}
  (I : InjectiveResolution F) (n : ℕ)

/-- Ext-defined actual sheaf cohomology as the homology of actual sections of
the supplied injective resolution. -/
def resolutionGlobalSectionsHomologyEquiv :
    Sheaf.H.{u} F n ≃+
      (((globalSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology n :=
  (ExtRightDerived.extAddEquivHomology (constantIntegers X) I n).trans
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) n).mapIso
      ((NatIso.mapHomologicalComplex (homGlobalSectionsIso X) (.up ℕ)).app
        I.cocomplex)).addCommGroupIsoToAddEquiv

/-- The unchanged actual sheaf-cohomology comparison is computed on any
supplied injective resolution, with its canonical right-derived comparison. -/
lemma HAddEquiv_eq_of_resolution (a : Sheaf.H.{u} F n) :
    HAddEquiv X F n a =
      (I.isoRightDerivedObj (globalSections X) n).inv
        (resolutionGlobalSectionsHomologyEquiv X I n a) := by
  have hn : (I.isoRightDerivedObj
        (preadditiveCoyoneda.obj (op (constantIntegers X))) n).inv ≫
      (homRightDerivedIso X n).hom.app F =
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) n).map
        ((NatTrans.mapHomologicalComplex (homGlobalSectionsIso X).hom _).app I.cocomplex) ≫
      (I.isoRightDerivedObj (globalSections X) n).inv := by
    change _ ≫ (NatTrans.rightDerived (homGlobalSectionsIso X).hom n).app F = _
    rw [InjectiveResolution.rightDerived_app_eq (homGlobalSectionsIso X).hom I n]
    simp only [Iso.inv_hom_id_assoc]
  simp only [HAddEquiv, AddEquiv.trans_apply]
  rw [ExtRightDerived.extAddEquivRightDerived_eq_of_resolution (constantIntegers X) I n]
  exact ConcreteCategory.congr_hom hn
    (ExtRightDerived.extAddEquivHomology (constantIntegers X) I n a)

end Langlands.Cohomology.AbelianSheafDerivedSections
