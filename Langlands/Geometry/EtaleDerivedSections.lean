import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Action.Basic

/-!
# Derived sections on the small étale site of an actual scheme

The sheaf category and its enough-injectives structure come from Mathlib's
scheme étale site. These constructions supply ordinary étale cohomology with
module coefficients, without assuming cohomology objects as input data.
-/

noncomputable section

namespace Langlands.Geometry.EtaleDerivedSections

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u uK vK w

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- Module sheaves on the genuine small étale site of the scheme. -/
abbrev ModuleSheaf := Sheaf X.smallEtaleTopology (ModuleCat.{u} R)

/-- The global-section functor supplied by the constant-sheaf adjunction. -/
def sections : ModuleSheaf X R ⥤ ModuleCat.{u} R :=
  CategoryTheory.Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u} R)

instance : (sections X R).Additive :=
  (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u} R)).right_adjoint_additive

instance : PreservesFiniteLimits (sections X R) :=
  inferInstanceAs (PreservesFiniteLimits
    (CategoryTheory.Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u} R)))

/-- Sections can also be evaluated on the terminal object of the small étale site. -/
def sectionsIso :
    sections X R ≅
      (sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
        (op (⊤_ X.Etale)) :=
  CategoryTheory.Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal

/-- Apply sections to a constructed injective resolution of the coefficient sheaf. -/
def complex (F : ModuleSheaf X R) : CochainComplex (ModuleCat.{u} R) ℕ :=
  ((sections X R).mapHomologicalComplex _).obj (injectiveResolution F).cocomplex

/-- The derived-section object is functorial in the homotopy category. -/
def homotopyFunctor :
    ModuleSheaf X R ⥤ HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℕ) :=
  (sections X R).rightDerivedToHomotopyCategory

/-- Ordinary small-étale cohomology with module coefficients. -/
def cohomology (n : ℕ) : ModuleSheaf X R ⥤ ModuleCat.{u} R :=
  (sections X R).rightDerived n

/-- The constructed complex represents the derived-section object. -/
def complexIso (F : ModuleSheaf X R) :
    (homotopyFunctor X R).obj F ≅
      (HomotopyCategory.quotient _ _).obj (complex X R F) :=
  (injectiveResolution F).isoRightDerivedToHomotopyCategoryObj _

/-- Its homology computes the derived-section functor. -/
def cohomologyIso (F : ModuleSheaf X R) (n : ℕ) :
    (cohomology X R n).obj F ≅ (complex X R F).homology n :=
  (injectiveResolution F).isoRightDerivedObj _ n

/-- Zeroth étale cohomology recovers ordinary sections. -/
def cohomologyZeroIso : cohomology X R 0 ≅ sections X R :=
  (sections X R).rightDerivedZeroIsoSelf

/-- Constant module coefficients are actual sheafifications of constant presheaves. -/
def constantCohomology (n : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  constantSheaf X.smallEtaleTopology (ModuleCat.{u} R) ⋙ cohomology X R n

/-- An algebraic action on a fixed-scheme coefficient sheaf acts on its cohomology. -/
def actionFunctor (G : Type w) [Monoid G] (n : ℕ) :
    Action (ModuleSheaf X R) G ⥤ Action (ModuleCat.{u} R) G :=
  (cohomology X R n).mapAction G

/-- Actual diagrams of coefficient sheaves induce diagrams of étale cohomology modules. -/
def diagramFunctor (K : Type uK) [Category.{vK} K] (n : ℕ) :
    (K ⥤ ModuleSheaf X R) ⥤ (K ⥤ ModuleCat.{u} R) :=
  (Functor.whiskeringRight K (ModuleSheaf X R) (ModuleCat.{u} R)).obj
    (cohomology X R n)

end Langlands.Geometry.EtaleDerivedSections
