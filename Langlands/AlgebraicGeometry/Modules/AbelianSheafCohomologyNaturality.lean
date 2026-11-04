import Langlands.AlgebraicGeometry.Modules.AbelianSheafComparisonNaturality
import Langlands.Cohomology.AbelianSheafDerivedSectionsNaturality

/-! # Coefficient naturality of actual module and abelian-sheaf cohomology -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

open PushforwardInjectiveAcyclic

variable (X : Scheme.{u})

/-- The existing comparison from actual abelian-sheaf cohomology to module
cohomology is natural in the coefficient module. -/
lemma HAddEquiv_naturality {M N : X.Modules} (f : M ⟶ N) (n : ℕ)
    (a : Sheaf.H.{u} ((toAbSheaf X).obj M) n) :
    HAddEquiv X N n (Sheaf.H.map ((toAbSheaf X).map f) n a) =
      (DerivedSections.cohomology X n).map f (HAddEquiv X M n a) := by
  simp only [HAddEquiv, AddEquiv.trans_apply]
  erw [AbelianSheafDerivedSections.HAddEquiv_naturality X.toTopCat
    ((toAbSheaf X).map f) n a]
  exact ConcreteCategory.congr_hom (cohomologyIso_inv_naturality X f n) _

/-- Coefficient naturality of the inverse of the existing module comparison. -/
lemma HAddEquiv_symm_naturality {M N : X.Modules} (f : M ⟶ N) (n : ℕ)
    (a : (DerivedSections.cohomology X n).obj M) :
    (HAddEquiv X N n).symm ((DerivedSections.cohomology X n).map f a) =
      Sheaf.H.map ((toAbSheaf X).map f) n ((HAddEquiv X M n).symm a) := by
  apply (HAddEquiv X N n).injective
  rw [AddEquiv.apply_symm_apply, HAddEquiv_naturality, AddEquiv.apply_symm_apply]

/-- The unchanged additive comparison components form a natural isomorphism
from actual cohomology of underlying abelian sheaves to underlying module
cohomology. -/
def HNatIso (n : ℕ) :
    toAbSheaf X ⋙ Sheaf.functorH (Opens.grothendieckTopology X.toTopCat) n ≅
      DerivedSections.cohomology X n ⋙
        forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun M => (HAddEquiv X M n).toAddCommGrpIso)
    (fun {M N} f => by
      ext a
      exact HAddEquiv_naturality X f n a)

/-- The natural isomorphism has exactly the published pointwise components. -/
@[simp]
lemma HNatIso_app (M : X.Modules) (n : ℕ) :
    (HNatIso X n).app M = (HAddEquiv X M n).toAddCommGrpIso := rfl

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
