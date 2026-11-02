import Langlands.AlgebraicGeometry.Modules.HigherDirectImageOpenRestriction
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof
import Langlands.Cohomology.AbelianSheafDerivedSections
import Langlands.Cohomology.AbelianSheafFlasque

/-! # Module cohomology and actual abelian-sheaf cohomology -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

open PushforwardInjectiveAcyclic

variable (X : Scheme.{u})

instance : (toAbSheaf X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive

/-- Forgetting the module structure commutes with actual global sections. -/
def globalSectionsIso :
    toAbSheaf X ⋙ AbelianSheafDerivedSections.globalSections X.toTopCat ≅
      DerivedSections.globalSections X ⋙
        forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- Exactness of module forgetting gives vanishing positive derived functors. -/
lemma isZero_rightDerived_toAbSheaf (M : X.Modules) (q : ℕ) :
    IsZero (((toAbSheaf X).rightDerived (q + 1)).obj M) :=
  DerivedSections.isZero_rightDerived_succ_of_preservesHomology _ M q

set_option backward.isDefEq.respectTransparency false in
/-- An injective module becomes acyclic for abelian global sections: its underlying
abelian sheaf is flasque. -/
lemma isZero_rightDerived_globalSections_of_injective (J : X.Modules) [Injective J]
    (q : ℕ) :
    IsZero (((AbelianSheafDerivedSections.globalSections X.toTopCat).rightDerived
      (q + 1)).obj ((toAbSheaf X).obj J)) := by
  have : TopCat.Sheaf.IsFlasque ((toAbSheaf X).obj J) :=
    isFlasque_of_injective J
  exact (AbelianSheafFlasque.isZero_H_succ_of_isFlasque q ((toAbSheaf X).obj J)).of_iso
    (AbelianSheafDerivedSections.HAddEquiv X.toTopCat ((toAbSheaf X).obj J)
      (q + 1)).toAddCommGrpIso.symm

/-- Deriving module global sections commutes with exact forgetting of the target
module structure. This uses the identity functor on the source category. -/
def forgetDerivedSectionsIso (n : ℕ) :
    DerivedSections.cohomology X n ⋙
        forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ≅
      (DerivedSections.globalSections X ⋙
        forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).rightDerived n :=
  DerivedComparison.rightDerivedCompIso (DerivedSections.globalSections X)
      (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}) (𝟭 _)
      (DerivedSections.globalSections X ⋙
        forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u})
      (Functor.leftUnitor _).symm n ≪≫ Functor.leftUnitor _

/-- The comparison of underlying module cohomology with right-derived global
sections of the actual underlying abelian sheaf. -/
def cohomologyIso (M : X.Modules) (n : ℕ) :
    (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        ((DerivedSections.cohomology X n).obj M) ≅
      ((AbelianSheafDerivedSections.globalSections X.toTopCat).rightDerived n).obj
        ((toAbSheaf X).obj M) := by
  haveI := isIso_compComparison (F := toAbSheaf X)
    (AbelianSheafDerivedSections.globalSections X.toTopCat) (globalSectionsIso X) M
    (isZero_rightDerived_toAbSheaf X M)
    (fun J _ q => isZero_rightDerived_globalSections_of_injective X J q) n
  exact (forgetDerivedSectionsIso X n).app M ≪≫
    asIso (compComparison (F := toAbSheaf X)
      (AbelianSheafDerivedSections.globalSections X.toTopCat)
      (globalSectionsIso X) M (isZero_rightDerived_toAbSheaf X M) n)

set_option backward.isDefEq.respectTransparency false in
/-- Mathlib's actual Ext-defined cohomology of the underlying abelian sheaf
agrees additively with the underlying module cohomology in every degree. -/
def HAddEquiv (M : X.Modules) (n : ℕ) :
    Sheaf.H.{u} ((toAbSheaf X).obj M) n ≃+
      (DerivedSections.cohomology X n).obj M :=
  (AbelianSheafDerivedSections.HAddEquiv X.toTopCat ((toAbSheaf X).obj M) n).trans
    (cohomologyIso X M n).symm.addCommGroupIsoToAddEquiv

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
