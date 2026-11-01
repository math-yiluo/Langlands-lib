import Langlands.Geometry.EtaleDerivedSystemPullback
import Langlands.Shimura.Coefficients.HarrisEtaleDerivedPlus

/-! # Actual geometric pullback of the full Harris derived coefficient system -/

noncomputable section

universe u wX wZ wV wT

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

local notation "R" => HarrisCoefficientIntegers L p
local notation "M" => harrisCoefficientDiagram ρ p U m
local notation "C" => harrisEtaleCoefficientSystem ρ p U m X Y hY

variable {Z : Scheme.{u}} (f : Z ⟶ X) [Etale f]

/-- Restrict the actual full Harris sheaf system and every coefficient map.
No identification with an independently associated torsor system is used. -/
def harrisEtaleRestrictedCoefficientSystem :
    ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf Z R :=
  C ⋙ EtalePullback.restriction f (ModuleCat.{u} R)

/-- Each restricted transition retains the original reduction and inverse
geometric torsor comparison, in that order. -/
theorem harrisEtaleRestrictedCoefficientSystem_map {i j : ℕᵒᵖ} (a : i ⟶ j) :
    (harrisEtaleRestrictedCoefficientSystem ρ p U m X Y hY f).map a =
      (EtalePullback.restriction f (ModuleCat.{u} R)).map
          ((etaleAssociatedReduction X Y a).app M) ≫
        (EtalePullback.restriction f (ModuleCat.{u} R)).map
          ((etaleAssociatedComparisonIso X Y hY a).inv.app M) :=
  (EtalePullback.restriction f (ModuleCat.{u} R)).map_comp _ _

/-- Ordinary sections of the actual restricted Harris sheaves. -/
def harrisEtaleRestrictedSectionsSystem : ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  harrisEtaleRestrictedCoefficientSystem ρ p U m X Y hY f ⋙
    EtaleDerivedSections.sections Z R

/-- Ordinary cohomology of the restricted system, including every transition. -/
def harrisEtaleRestrictedCohomologySystem (q : ℕ) : ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  harrisEtaleRestrictedCoefficientSystem ρ p U m X Y hY f ⋙
    EtaleDerivedSections.cohomology Z R q

/-- Actual geometric restriction of the entire ordinary section system. -/
def harrisEtaleSectionsPullback :
    harrisEtaleSectionsSystem ρ p U m X Y hY ⟶
      harrisEtaleRestrictedSectionsSystem ρ p U m X Y hY f :=
  EtalePullback.systemSectionsMap f R C

/-- Actual geometric pullback of ordinary Harris cohomology in every exponent. -/
def harrisEtaleCohomologyPullback (q : ℕ) :
    harrisEtaleCohomologySystem ρ p U m X Y hY q ⟶
      harrisEtaleRestrictedCohomologySystem ρ p U m X Y hY f q :=
  EtalePullback.systemCohomologyMap f R C q

variable [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X (HarrisCoefficientIntegers L p))]
  [HasDerivedCategory.{wZ} (EtaleDerivedSections.ModuleSheaf Z (HarrisCoefficientIntegers L p))]
  [HasDerivedCategory.{wT} (ModuleCat.{u} (HarrisCoefficientIntegers L p))]

/-- Actual bounded-below derived sections of the restricted Harris system. -/
def harrisEtaleRestrictedDerivedPlusSystem :
    ℕᵒᵖ ⥤ DerivedCategory.Plus (ModuleCat.{u} R) :=
  harrisEtaleRestrictedCoefficientSystem ρ p U m X Y hY f ⋙
    EtaleDerivedSectionsPlus.derivedSections Z R

/-- Canonical ordinary-cohomology recovery for the whole restricted system. -/
def harrisEtaleRestrictedDerivedPlusCohomologyIso (q : ℕ) :
    harrisEtaleRestrictedDerivedPlusSystem ρ p U m X Y hY f ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q ≅
      harrisEtaleRestrictedCohomologySystem ρ p U m X Y hY f q :=
  EtalePullback.systemDerivedSectionsHomologyIso Z R
    (harrisEtaleRestrictedCoefficientSystem ρ p U m X Y hY f) q

/-- Canonical degree-zero section recovery for the whole restricted system. -/
def harrisEtaleRestrictedDerivedPlusZeroIso :
    harrisEtaleRestrictedDerivedPlusSystem ρ p U m X Y hY f ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0 ≅
      harrisEtaleRestrictedSectionsSystem ρ p U m X Y hY f :=
  EtalePullback.systemDerivedSectionsZeroIso Z R
    (harrisEtaleRestrictedCoefficientSystem ρ p U m X Y hY f)

/-- Geometric pullback of the full actual derived Harris coefficient system. -/
def harrisEtaleDerivedPlusPullback :
    harrisEtaleDerivedPlusSystem ρ p U m X Y hY ⟶
      harrisEtaleRestrictedDerivedPlusSystem ρ p U m X Y hY f :=
  EtalePullback.systemDerivedSectionsMap f R C

/-- The map in each exponent is the actual derived geometric pullback of its
constructed Harris coefficient sheaf. -/
@[simp]
theorem harrisEtaleDerivedPlusPullback_app (n : ℕᵒᵖ) :
    (harrisEtaleDerivedPlusPullback ρ p U m X Y hY f).app n =
      (EtalePullback.derivedSectionsMap f R).app ((C).obj n) := rfl

/-- Pullback commutes with every original Harris coefficient transition. -/
@[reassoc]
theorem harrisEtaleDerivedPlusPullback_naturality {i j : ℕᵒᵖ} (a : i ⟶ j) :
    (harrisEtaleDerivedPlusSystem ρ p U m X Y hY).map a ≫
        (harrisEtaleDerivedPlusPullback ρ p U m X Y hY f).app j =
      (harrisEtaleDerivedPlusPullback ρ p U m X Y hY f).app i ≫
        (harrisEtaleRestrictedDerivedPlusSystem ρ p U m X Y hY f).map a :=
  (harrisEtaleDerivedPlusPullback ρ p U m X Y hY f).naturality a

/-- The generic canonical comparison is the existing Harris comparison. -/
theorem harrisEtaleDerivedPlusCohomologyIso_eq_system (q : ℕ) :
    harrisEtaleDerivedPlusCohomologyIso ρ p U m X Y hY q =
      EtalePullback.systemDerivedSectionsHomologyIso X R C q := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The generic canonical section comparison agrees with the previously
constructed degree-zero Harris comparison. -/
theorem harrisEtaleDerivedPlusZeroIso_eq_system :
    harrisEtaleDerivedPlusZeroIso ρ p U m X Y hY =
      EtalePullback.systemDerivedSectionsZeroIso X R C := by
  dsimp only [harrisEtaleDerivedPlusZeroIso, harrisEtaleDerivedPlusCohomologyIso,
    harrisEtaleCohomologyZeroIso, EtalePullback.systemDerivedSectionsZeroIso,
    EtaleDerivedSectionsPlus.homologyZeroIso]
  rw [Functor.isoWhiskerLeft_trans, Iso.trans_assoc]
  rfl

/-- Under the specified canonical Harris comparisons, homology of actual
geometric derived pullback is ordinary cohomology pullback. -/
theorem harrisEtaleDerivedPlusPullback_homology (q : ℕ) :
    Functor.whiskerRight (harrisEtaleDerivedPlusPullback ρ p U m X Y hY f)
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q) ≫
        (harrisEtaleRestrictedDerivedPlusCohomologyIso ρ p U m X Y hY f q).hom =
      (harrisEtaleDerivedPlusCohomologyIso ρ p U m X Y hY q).hom ≫
        harrisEtaleCohomologyPullback ρ p U m X Y hY f q :=
  EtalePullback.systemDerivedSectionsMap_homology f R C q

/-- Degree zero of the same map recovers ordinary global-section restriction. -/
theorem harrisEtaleDerivedPlusPullback_zero :
    Functor.whiskerRight (harrisEtaleDerivedPlusPullback ρ p U m X Y hY f)
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0) ≫
        (harrisEtaleRestrictedDerivedPlusZeroIso ρ p U m X Y hY f).hom =
      (harrisEtaleDerivedPlusZeroIso ρ p U m X Y hY).hom ≫
        harrisEtaleSectionsPullback ρ p U m X Y hY f := by
  rw [harrisEtaleDerivedPlusZeroIso_eq_system]
  exact EtalePullback.systemDerivedSectionsMap_zero f R C

/-- Pullback along the identity, followed by the actual identity-restriction
comparison, is the identity of the full derived Harris system. -/
theorem harrisEtaleDerivedPlusPullback_id :
    harrisEtaleDerivedPlusPullback ρ p U m X Y hY (𝟙 X) ≫
        Functor.whiskerRight
          (Functor.whiskerLeft C (EtalePullback.restrictionId (ModuleCat.{u} R)).hom)
          (EtaleDerivedSectionsPlus.derivedSections X R) = 𝟙 _ :=
  EtalePullback.systemDerivedSectionsMap_id R C

variable {V : Scheme.{u}}
variable [HasDerivedCategory.{wV} (EtaleDerivedSections.ModuleSheaf V (HarrisCoefficientIntegers L p))]

/-- Successive geometric pullbacks of the same full Harris system agree in
the derived category with pullback along the composite, after restrictionComp. -/
theorem harrisEtaleDerivedPlusPullback_comp (g : V ⟶ Z) [Etale g] :
    harrisEtaleDerivedPlusPullback ρ p U m X Y hY f ≫
        EtalePullback.systemDerivedSectionsMap g R
          (harrisEtaleRestrictedCoefficientSystem ρ p U m X Y hY f) ≫
        Functor.whiskerRight
          (Functor.whiskerLeft C
            (EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom)
          (EtaleDerivedSectionsPlus.derivedSections V R) =
      harrisEtaleDerivedPlusPullback ρ p U m X Y hY (g ≫ f) :=
  EtalePullback.systemDerivedSectionsMap_comp f R g C

end Langlands.Shimura.Coefficients
