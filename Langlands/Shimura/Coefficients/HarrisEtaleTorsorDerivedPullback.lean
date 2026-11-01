import Langlands.Shimura.Coefficients.HarrisEtaleTorsorPullback

/-! # Derived Harris pullback with the actual associated geometric target -/

noncomputable section

universe u wX wZ wT

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

variable [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X (HarrisCoefficientIntegers L p))]
  [HasDerivedCategory.{wZ} (EtaleDerivedSections.ModuleSheaf Z (HarrisCoefficientIntegers L p))]
  [HasDerivedCategory.{wT} (ModuleCat.{u} (HarrisCoefficientIntegers L p))]

/-- Derived sections identify the restricted system with the system associated
independently to the actual pulled-back Harris torsors. -/
def harrisEtaleTorsorDerivedPlusIso :
    harrisEtaleRestrictedDerivedPlusSystem ρ p U m X Y hY f ≅
      harrisEtaleDerivedPlusSystem ρ p U m Z Yf hYf :=
  Functor.isoWhiskerRight (harrisEtaleCoefficientSystemPullback ρ p U m X Y hY f)
    (EtaleDerivedSectionsPlus.derivedSections Z R)

/-- Geometric derived pullback, with target the actual independently associated
Harris system on the scheme fiber products. -/
def harrisEtaleTorsorDerivedPlusPullback :
    harrisEtaleDerivedPlusSystem ρ p U m X Y hY ⟶
      harrisEtaleDerivedPlusSystem ρ p U m Z Yf hYf :=
  harrisEtaleDerivedPlusPullback ρ p U m X Y hY f ≫
    (harrisEtaleTorsorDerivedPlusIso ρ p U m X Y hY f).hom

/-- Every component first uses geometric derived pullback, then derived
sections of the constructed coefficient comparison. -/
@[simp] theorem harrisEtaleTorsorDerivedPlusPullback_app (n : ℕᵒᵖ) :
    (harrisEtaleTorsorDerivedPlusPullback ρ p U m X Y hY f).app n =
      (harrisEtaleDerivedPlusPullback ρ p U m X Y hY f).app n ≫
        (EtaleDerivedSectionsPlus.derivedSections Z R).map
          ((etaleConstantAssociatedPullback f R (Y.action n)).hom.app ((M).action n)) :=
  rfl

/-- The constructed map respects every original and new Harris transition. -/
@[reassoc] theorem harrisEtaleTorsorDerivedPlusPullback_naturality
    {i j : ℕᵒᵖ} (a : i ⟶ j) :
    (harrisEtaleDerivedPlusSystem ρ p U m X Y hY).map a ≫
        (harrisEtaleTorsorDerivedPlusPullback ρ p U m X Y hY f).app j =
      (harrisEtaleTorsorDerivedPlusPullback ρ p U m X Y hY f).app i ≫
        (harrisEtaleDerivedPlusSystem ρ p U m Z Yf hYf).map a :=
  (harrisEtaleTorsorDerivedPlusPullback ρ p U m X Y hY f).naturality a

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X (HarrisCoefficientIntegers L p))] in
/-- The canonical recovery isomorphisms intertwine the derived target
identification and the ordinary cohomological target identification. -/
theorem harrisEtaleTorsorDerivedPlusIso_homology (q : ℕ) :
    Functor.whiskerRight
          (harrisEtaleTorsorDerivedPlusIso ρ p U m X Y hY f).hom
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q) ≫
        (harrisEtaleDerivedPlusCohomologyIso ρ p U m Z Yf hYf q).hom =
      (harrisEtaleRestrictedDerivedPlusCohomologyIso ρ p U m X Y hY f q).hom ≫
        (harrisEtaleTorsorCohomologyIso ρ p U m X Y hY f q).hom := by
  apply NatTrans.ext
  funext n
  simpa only [harrisEtaleTorsorDerivedPlusIso, harrisEtaleTorsorCohomologyIso,
    harrisEtaleDerivedPlusCohomologyIso, harrisEtaleRestrictedDerivedPlusCohomologyIso,
    harrisEtaleDerivedPlusSystem, harrisEtaleRestrictedDerivedPlusSystem,
    harrisEtaleCohomologySystem, harrisEtaleRestrictedCohomologySystem,
    EtalePullback.systemDerivedSectionsHomologyIso,
    Functor.comp_map, Functor.comp_obj, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.id_comp] using
    (EtaleDerivedSectionsPlus.homologyNatIso Z R q).hom.naturality
      ((harrisEtaleCoefficientSystemPullback ρ p U m X Y hY f).hom.app n)

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X (HarrisCoefficientIntegers L p))] in
/-- The same target-identification square in degree zero recovers the actual
ordinary section systems under the specified Harris comparisons. -/
theorem harrisEtaleTorsorDerivedPlusIso_zero :
    Functor.whiskerRight
          (harrisEtaleTorsorDerivedPlusIso ρ p U m X Y hY f).hom
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0) ≫
        (harrisEtaleDerivedPlusZeroIso ρ p U m Z Yf hYf).hom =
      (harrisEtaleRestrictedDerivedPlusZeroIso ρ p U m X Y hY f).hom ≫
        (harrisEtaleTorsorSectionsIso ρ p U m X Y hY f).hom := by
  rw [harrisEtaleDerivedPlusZeroIso_eq_system]
  apply NatTrans.ext
  funext n
  simpa only [harrisEtaleTorsorDerivedPlusIso, harrisEtaleTorsorSectionsIso,
    harrisEtaleDerivedPlusSystem, harrisEtaleRestrictedDerivedPlusSystem,
    harrisEtaleSectionsSystem, harrisEtaleRestrictedSectionsSystem,
    harrisEtaleRestrictedDerivedPlusZeroIso, EtalePullback.systemDerivedSectionsZeroIso,
    Functor.comp_map, Functor.comp_obj, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.id_comp] using
    (EtaleDerivedSectionsPlus.homologyZeroIso Z R).hom.naturality
      ((harrisEtaleCoefficientSystemPullback ρ p U m X Y hY f).hom.app n)

/-- In every nonnegative degree, homology of the actual derived geometric map
is ordinary cohomology pullback to the independently associated new torsors. -/
theorem harrisEtaleTorsorDerivedPlusPullback_homology (q : ℕ) :
    Functor.whiskerRight (harrisEtaleTorsorDerivedPlusPullback ρ p U m X Y hY f)
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q) ≫
        (harrisEtaleDerivedPlusCohomologyIso ρ p U m Z Yf hYf q).hom =
      (harrisEtaleDerivedPlusCohomologyIso ρ p U m X Y hY q).hom ≫
        harrisEtaleTorsorCohomologyPullback ρ p U m X Y hY f q := by
  dsimp only [harrisEtaleTorsorDerivedPlusPullback, harrisEtaleTorsorCohomologyPullback]
  rw [Functor.whiskerRight_comp, Category.assoc, harrisEtaleTorsorDerivedPlusIso_homology,
    ← Category.assoc, harrisEtaleDerivedPlusPullback_homology, Category.assoc]

/-- Degree zero of that same derived map recovers actual section restriction
with target on the geometrically pulled-back Harris torsors. -/
theorem harrisEtaleTorsorDerivedPlusPullback_zero :
    Functor.whiskerRight (harrisEtaleTorsorDerivedPlusPullback ρ p U m X Y hY f)
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0) ≫
        (harrisEtaleDerivedPlusZeroIso ρ p U m Z Yf hYf).hom =
      (harrisEtaleDerivedPlusZeroIso ρ p U m X Y hY).hom ≫
        harrisEtaleTorsorSectionsPullback ρ p U m X Y hY f := by
  dsimp only [harrisEtaleTorsorDerivedPlusPullback, harrisEtaleTorsorSectionsPullback]
  rw [Functor.whiskerRight_comp, Category.assoc, harrisEtaleTorsorDerivedPlusIso_zero,
    ← Category.assoc, harrisEtaleDerivedPlusPullback_zero, Category.assoc]

end Langlands.Shimura.Coefficients
