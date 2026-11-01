import Langlands.Shimura.Coefficients.EtaleVaryingSystemPullback
import Langlands.Shimura.Coefficients.HarrisEtaleDerivedPullback

/-! # Harris coefficients on the actual geometrically pulled-back torsors -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory AlgebraicGeometry Opposite Langlands.Global
open Langlands.Geometry

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints) (m : ℕ)
variable (X : Scheme.{u})
variable (Y : EquivariantDiagram (harrisCongruenceGroups ρ p U m) X.Etale)
variable (hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n))
variable {Z : Scheme.{u}} (f : Z ⟶ X) [Etale f]

local notation "R" => HarrisCoefficientIntegers L p
local notation "M" => harrisCoefficientDiagram ρ p U m
local notation "Yf" =>
  Functor.obj (etaleTorsorDiagramPullback f (harrisCongruenceGroups ρ p U m)) Y
local notation "hYf" =>
  etaleTorsorDiagramPullback_isFiniteGeometricTorsor f (harrisCongruenceGroups ρ p U m) Y hY

/-- The full restricted Harris system is the associated system on the actual
scheme fiber products, with every inverse-cover transition retained. -/
def harrisEtaleCoefficientSystemPullback :
    harrisEtaleRestrictedCoefficientSystem ρ p U m X Y hY f ≅
      harrisEtaleCoefficientSystem ρ p U m Z Yf hYf :=
  (etaleAssociatedVaryingSystemPullback f R Y hY).app M

/-- At every exponent this is the canonical constant-associated comparison. -/
@[simp] theorem harrisEtaleCoefficientSystemPullback_hom_app (n : ℕᵒᵖ) :
    (harrisEtaleCoefficientSystemPullback ρ p U m X Y hY f).hom.app n =
      (etaleConstantAssociatedPullback f R (Y.action n)).hom.app ((M).action n) := rfl

/-- Its inverse uses the inverse of the same constructed comparison. -/
@[simp] theorem harrisEtaleCoefficientSystemPullback_inv_app (n : ℕᵒᵖ) :
    (harrisEtaleCoefficientSystemPullback ρ p U m X Y hY f).inv.app n =
      (etaleConstantAssociatedPullback f R (Y.action n)).inv.app ((M).action n) := rfl

/-- Actual reduction followed by inverse cover comparison commutes with the
geometric identification of the two Harris systems. -/
@[reassoc] theorem harrisEtaleCoefficientSystemPullback_naturality
    {i j : ℕᵒᵖ} (a : i ⟶ j) :
    (harrisEtaleRestrictedCoefficientSystem ρ p U m X Y hY f).map a ≫
        (harrisEtaleCoefficientSystemPullback ρ p U m X Y hY f).hom.app j =
      (harrisEtaleCoefficientSystemPullback ρ p U m X Y hY f).hom.app i ≫
        (harrisEtaleCoefficientSystem ρ p U m Z Yf hYf).map a :=
  (harrisEtaleCoefficientSystemPullback ρ p U m X Y hY f).hom.naturality a

/-- Identify sections of restricted coefficients with sections of the
independently associated coefficients on the pulled-back torsors. -/
def harrisEtaleTorsorSectionsIso :
    harrisEtaleRestrictedSectionsSystem ρ p U m X Y hY f ≅
      harrisEtaleSectionsSystem ρ p U m Z Yf hYf :=
  Functor.isoWhiskerRight (harrisEtaleCoefficientSystemPullback ρ p U m X Y hY f)
    (EtaleDerivedSections.sections Z R)

/-- The same identification in every ordinary cohomological degree. -/
def harrisEtaleTorsorCohomologyIso (q : ℕ) :
    harrisEtaleRestrictedCohomologySystem ρ p U m X Y hY f q ≅
      harrisEtaleCohomologySystem ρ p U m Z Yf hYf q :=
  Functor.isoWhiskerRight (harrisEtaleCoefficientSystemPullback ρ p U m X Y hY f)
    (EtaleDerivedSections.cohomology Z R q)

/-- Geometric restriction of sections, with target on the actual new torsors. -/
def harrisEtaleTorsorSectionsPullback :
    harrisEtaleSectionsSystem ρ p U m X Y hY ⟶
      harrisEtaleSectionsSystem ρ p U m Z Yf hYf :=
  harrisEtaleSectionsPullback ρ p U m X Y hY f ≫
    (harrisEtaleTorsorSectionsIso ρ p U m X Y hY f).hom

/-- Geometric pullback of cohomology with independently associated target. -/
def harrisEtaleTorsorCohomologyPullback (q : ℕ) :
    harrisEtaleCohomologySystem ρ p U m X Y hY q ⟶
      harrisEtaleCohomologySystem ρ p U m Z Yf hYf q :=
  harrisEtaleCohomologyPullback ρ p U m X Y hY f q ≫
    (harrisEtaleTorsorCohomologyIso ρ p U m X Y hY f q).hom

/-- The section map applies actual geometric restriction, then the canonical
comparison for the same full Harris lattice reduction. -/
@[simp] theorem harrisEtaleTorsorSectionsPullback_app (n : ℕᵒᵖ) :
    (harrisEtaleTorsorSectionsPullback ρ p U m X Y hY f).app n =
      (harrisEtaleSectionsPullback ρ p U m X Y hY f).app n ≫
        (EtaleDerivedSections.sections Z R).map
          ((etaleConstantAssociatedPullback f R (Y.action n)).hom.app ((M).action n)) :=
  rfl

/-- Each cohomology map retains the actual geometric map and coefficient
comparison, in that order. -/
@[simp] theorem harrisEtaleTorsorCohomologyPullback_app (q : ℕ) (n : ℕᵒᵖ) :
    (harrisEtaleTorsorCohomologyPullback ρ p U m X Y hY f q).app n =
      (harrisEtaleCohomologyPullback ρ p U m X Y hY f q).app n ≫
        (EtaleDerivedSections.cohomology Z R q).map
          ((etaleConstantAssociatedPullback f R (Y.action n)).hom.app ((M).action n)) :=
  rfl

/-- Pullback commutes with all original and new Harris coefficient transitions. -/
@[reassoc] theorem harrisEtaleTorsorCohomologyPullback_naturality
    (q : ℕ) {i j : ℕᵒᵖ} (a : i ⟶ j) :
    (harrisEtaleCohomologySystem ρ p U m X Y hY q).map a ≫
        (harrisEtaleTorsorCohomologyPullback ρ p U m X Y hY f q).app j =
      (harrisEtaleTorsorCohomologyPullback ρ p U m X Y hY f q).app i ≫
        (harrisEtaleCohomologySystem ρ p U m Z Yf hYf q).map a :=
  (harrisEtaleTorsorCohomologyPullback ρ p U m X Y hY f q).naturality a

end Langlands.Shimura.Coefficients
