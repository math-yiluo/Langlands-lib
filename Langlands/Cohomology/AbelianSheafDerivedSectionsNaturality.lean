import Langlands.Cohomology.AbelianSheafDerivedSections
import Langlands.Cohomology.ExtRightDerivedNaturality

/-! # Coefficient naturality of actual abelian-sheaf cohomology comparisons -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace

namespace Langlands.Cohomology.AbelianSheafDerivedSections

variable (X : TopCat.{u})

/-- The existing additive comparison is natural for Mathlib's actual map on
Ext-defined sheaf cohomology. -/
lemma HAddEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ) (a : Sheaf.H.{u} F n) :
    HAddEquiv X G n (Sheaf.H.map f n a) =
      ((globalSections X).rightDerived n).map f (HAddEquiv X F n a) := by
  simp only [HAddEquiv, AddEquiv.trans_apply, Sheaf.H.map_apply]
  rw [ExtRightDerived.extAddEquivRightDerived_naturality]
  exact ConcreteCategory.congr_hom ((homRightDerivedIso X n).hom.naturality f) _

/-- Coefficient naturality of the inverse of the existing comparison. -/
lemma HAddEquiv_symm_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ) (a : ((globalSections X).rightDerived n).obj F) :
    (HAddEquiv X G n).symm (((globalSections X).rightDerived n).map f a) =
      Sheaf.H.map f n ((HAddEquiv X F n).symm a) := by
  apply (HAddEquiv X G n).injective
  rw [AddEquiv.apply_symm_apply, HAddEquiv_naturality, AddEquiv.apply_symm_apply]

/-- The unchanged comparison components form a natural isomorphism from
Mathlib's actual sheaf-cohomology functor to right-derived global sections. -/
def HNatIso (n : ℕ) :
    Sheaf.functorH (Opens.grothendieckTopology X) n ≅
      (globalSections X).rightDerived n :=
  NatIso.ofComponents (fun F => (HAddEquiv X F n).toAddCommGrpIso)
    (fun {F G} f => by
      ext a
      exact HAddEquiv_naturality X f n a)

/-- The natural isomorphism retains the published pointwise comparison. -/
@[simp]
lemma HNatIso_app (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (HNatIso X n).app F = (HAddEquiv X F n).toAddCommGrpIso := rfl

end Langlands.Cohomology.AbelianSheafDerivedSections
