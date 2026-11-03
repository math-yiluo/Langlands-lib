import Langlands.AlgebraicGeometry.FiniteLinearEquationsScheme
import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Langlands.Cohomology.PerfectModuleComplex
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-! # Homology after tensoring with global sections of scheme tests -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry

namespace TensorSections

variable {R : CommRingCat.{u}}

attribute [local instance] FiniteLinearEquations.sectionsAlgebra

/-- Global sections of each scheme over `Spec R`, regarded as an `R`-module. -/
def sectionModules : (Over (Spec R))ᵒᵖ ⥤ ModuleCat.{u} R where
  obj T := ModuleCat.of R Γ(T.unop.left, ⊤)
  map q := ModuleCat.ofHom (FiniteLinearEquations.pullSections q.unop).toLinearMap
  map_id T := by
    ext x
    change (𝟙 T.unop.left : T.unop.left ⟶ T.unop.left).appTop x = x
    simp
  map_comp q r := by
    ext x
    change (r.unop.left ≫ q.unop.left).appTop x =
      r.unop.left.appTop (q.unop.left.appTop x)
    rw [Scheme.Hom.comp_appTop]
    rfl

/-- Tensor a fixed cochain complex with a varying module in every degree. -/
def tensorComplex (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj A :=
    ((MonoidalCategory.tensorLeft A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  map f :=
    (NatTrans.mapHomologicalComplex
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map f)
      (ComplexShape.up ℤ)).app K
  map_id A := by
    apply HomologicalComplex.hom_ext
    intro i
    exact NatTrans.congr_app
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map_id A) (K.X i)
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro i
    exact NatTrans.congr_app
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map_comp f g) (K.X i)

/-- The actual tensor complex `Γ(T,𝒪_T) ⊗[R] K`, retaining the coefficient
ring `R` on its terms and maps. -/
def complexes (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (Over (Spec R))ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  sectionModules ⋙ tensorComplex K

/-- Integer cohomology of the global-section tensor complexes, with the
explicit value lift used by scheme presheaves in this Library. -/
def homologyPresheaf (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    AlgebraicSpace.Presheaf (Spec R) :=
  complexes K ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n ⋙
    forget (ModuleCat.{u} R) ⋙ uliftFunctor.{u + 1}

end TensorSections

end Langlands.AlgebraicGeometry
