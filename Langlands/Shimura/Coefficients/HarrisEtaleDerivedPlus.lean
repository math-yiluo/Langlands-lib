import Langlands.Geometry.EtaleDerivedSectionsPlus
import Langlands.Shimura.Coefficients.HarrisEtaleCoefficients

/-! # Bounded-below derived global sections of the full Harris coefficient system -/

noncomputable section

universe u wS wT

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Langlands.Global

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints) (m : ℕ)
variable (X : Scheme.{u})
variable (Y : EquivariantDiagram (harrisCongruenceGroups ρ p U m) X.Etale)
variable (hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n))

local notation "R" => HarrisCoefficientIntegers L p
local notation "M" => harrisCoefficientDiagram ρ p U m
local notation "C" => harrisEtaleCoefficientSystem ρ p U m X Y hY

variable [HasDerivedCategory.{wS}
    (Langlands.Geometry.EtaleDerivedSections.ModuleSheaf X (HarrisCoefficientIntegers L p))]
  [HasDerivedCategory.{wT} (ModuleCat.{u} (HarrisCoefficientIntegers L p))]

/-- The full Harris coefficient system, followed by actual derived global
sections in the bounded-below derived category. -/
def harrisEtaleDerivedPlusSystem :
    ℕᵒᵖ ⥤ DerivedCategory.Plus (ModuleCat.{u} R) :=
  C ⋙ Langlands.Geometry.EtaleDerivedSectionsPlus.derivedSections X R

/-- An integer-indexed bounded-below section complex at each exponent. -/
def harrisEtaleDerivedPlusComplex (n : ℕᵒᵖ) :
    CochainComplex.Plus (ModuleCat.{u} R) :=
  Langlands.Geometry.EtaleDerivedSectionsPlus.complex X R ((C).obj n)

/-- The section complex represents the actual derived object at each exponent. -/
def harrisEtaleDerivedPlusSystemIso (n : ℕᵒᵖ) :
    (harrisEtaleDerivedPlusSystem ρ p U m X Y hY).obj n ≅
      DerivedCategory.Plus.Q.obj (harrisEtaleDerivedPlusComplex ρ p U m X Y hY n) :=
  Langlands.Geometry.EtaleDerivedSectionsPlus.complexIso X R ((C).obj n)

/-- A chosen cochain lift of the genuine Harris reduction/comparison transition. -/
def harrisEtaleDerivedPlusComplexMap {i j : ℕᵒᵖ} (f : i ⟶ j) :
    harrisEtaleDerivedPlusComplex ρ p U m X Y hY i ⟶
      harrisEtaleDerivedPlusComplex ρ p U m X Y hY j :=
  Langlands.Geometry.EtaleDerivedSectionsPlus.complexMap X R ((C).map f)

/-- After localization, the chosen cochain transition is the actual derived
Harris transition. -/
@[reassoc]
theorem harrisEtaleDerivedPlusSystemIso_hom_naturality
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (harrisEtaleDerivedPlusSystem ρ p U m X Y hY).map f ≫
        (harrisEtaleDerivedPlusSystemIso ρ p U m X Y hY j).hom =
      (harrisEtaleDerivedPlusSystemIso ρ p U m X Y hY i).hom ≫
        DerivedCategory.Plus.Q.map (harrisEtaleDerivedPlusComplexMap ρ p U m X Y hY f) :=
  Langlands.Geometry.EtaleDerivedSectionsPlus.complexIso_hom_naturality X R ((C).map f)

/-- Derived transitions preserve the original reduction followed by the inverse
of the proved comparison between the two geometric torsors. -/
theorem harrisEtaleDerivedPlusSystem_map {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (harrisEtaleDerivedPlusSystem ρ p U m X Y hY).map f =
      (Langlands.Geometry.EtaleDerivedSectionsPlus.derivedSections X R).map
          ((etaleAssociatedReduction X Y f).app M) ≫
        (Langlands.Geometry.EtaleDerivedSectionsPlus.derivedSections X R).map
          ((etaleAssociatedComparisonIso X Y hY f).inv.app M) :=
  (Langlands.Geometry.EtaleDerivedSectionsPlus.derivedSections X R).map_comp _ _

/-- Cohomology of the entire derived system is naturally the already constructed
ordinary Harris etale-cohomology system. -/
def harrisEtaleDerivedPlusCohomologyIso (q : ℕ) :
    harrisEtaleDerivedPlusSystem ρ p U m X Y hY ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q ≅
      harrisEtaleCohomologySystem ρ p U m X Y hY q :=
  Functor.associator C
      (Langlands.Geometry.EtaleDerivedSectionsPlus.derivedSections X R)
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q) ≪≫
    Functor.isoWhiskerLeft C
      (Langlands.Geometry.EtaleDerivedSectionsPlus.homologyNatIso X R q)

set_option backward.isDefEq.respectTransparency false in
/-- The cohomology comparison recovers the genuine reduction and inverse-torsor
comparison maps, at every transition of the full Harris system. -/
@[reassoc]
theorem harrisEtaleDerivedPlusCohomologyIso_hom_naturality
    (q : ℕ) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).map
          ((harrisEtaleDerivedPlusSystem ρ p U m X Y hY).map f) ≫
        (harrisEtaleDerivedPlusCohomologyIso ρ p U m X Y hY q).hom.app j =
      (harrisEtaleDerivedPlusCohomologyIso ρ p U m X Y hY q).hom.app i ≫
        (Langlands.Geometry.EtaleDerivedSections.cohomology X R q).map
          ((etaleAssociatedReduction X Y f).app M) ≫
        (Langlands.Geometry.EtaleDerivedSections.cohomology X R q).map
          ((etaleAssociatedComparisonIso X Y hY f).inv.app M) := by
  have h := (harrisEtaleDerivedPlusCohomologyIso ρ p U m X Y hY q).hom.naturality f
  simpa only [Functor.comp_obj, Functor.comp_map, harrisEtaleCohomologySystem_map, Category.assoc] using h

/-- Degree-zero cohomology recovers the ordinary section system naturally. -/
def harrisEtaleDerivedPlusZeroIso :
    harrisEtaleDerivedPlusSystem ρ p U m X Y hY ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0 ≅
      harrisEtaleSectionsSystem ρ p U m X Y hY :=
  harrisEtaleDerivedPlusCohomologyIso ρ p U m X Y hY 0 ≪≫
    harrisEtaleCohomologyZeroIso ρ p U m X Y hY

/-- Each derived Harris coefficient object has zero negative cohomology. -/
theorem harrisEtaleDerivedPlus_isZero_homology_of_neg (n : ℕᵒᵖ)
    {q : ℤ} (hq : q < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).obj
      ((harrisEtaleDerivedPlusSystem ρ p U m X Y hY).obj n)) :=
  Langlands.Geometry.EtaleDerivedSectionsPlus.isZero_homology_of_neg X R ((C).obj n) hq

end Langlands.Shimura.Coefficients
