import Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
import Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange

/-! # Coefficient naturality of the actual module/sheaf derived comparison -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

open PushforwardInjectiveAcyclic

variable (X : Scheme.{u})

/-- The existing pointwise derived comparison is natural in the module. -/
@[reassoc]
theorem cohomologyIso_hom_naturality {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map
        ((DerivedSections.cohomology X n).map f) ≫ (cohomologyIso X N n).hom =
      (cohomologyIso X M n).hom ≫
        ((AbelianSheafDerivedSections.globalSections X.toTopCat).rightDerived n).map
          ((toAbSheaf X).map f) := by
  have h₁ := (forgetDerivedSectionsIso X n).hom.naturality f
  have h₂ := compComparison_naturality (F := toAbSheaf X)
    (AbelianSheafDerivedSections.globalSections X.toTopCat) (globalSectionsIso X) f
    (isZero_rightDerived_toAbSheaf X M) (isZero_rightDerived_toAbSheaf X N) n
  simp only [Functor.comp_map] at h₁
  simp only [cohomologyIso, Iso.trans_hom, asIso_hom, Iso.app_hom, Category.assoc]
  rw [reassoc_of% h₁, h₂]

/-- The inverse comparison is natural in the module as well. -/
@[reassoc]
theorem cohomologyIso_inv_naturality {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    ((AbelianSheafDerivedSections.globalSections X.toTopCat).rightDerived n).map
        ((toAbSheaf X).map f) ≫ (cohomologyIso X N n).inv =
      (cohomologyIso X M n).inv ≫
        (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map
          ((DerivedSections.cohomology X n).map f) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (cohomologyIso_hom_naturality X f n).symm

/-- The published componentwise comparison assembled into a natural isomorphism. -/
def cohomologyNatIso (n : ℕ) :
    DerivedSections.cohomology X n ⋙
        forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ≅
      toAbSheaf X ⋙
        (AbelianSheafDerivedSections.globalSections X.toTopCat).rightDerived n :=
  NatIso.ofComponents (fun M => cohomologyIso X M n)
    (fun f => cohomologyIso_hom_naturality X f n)

@[simp]
lemma cohomologyNatIso_app (M : X.Modules) (n : ℕ) :
    (cohomologyNatIso X n).app M = cohomologyIso X M n := rfl

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
