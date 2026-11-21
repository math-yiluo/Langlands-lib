import Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology
import Langlands.Shimura.Unitary.HarrisCMTypePlaces
import Langlands.AlgebraicGeometry.ProjectiveSpace.BaseChange

/-! # A smooth projective model of the actual tame Harris tower over a finite-place trait -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NumberField

set_option autoImplicit false
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Global AdelicFunctoriality Langlands.Shimura.CompactOpenLevel
open Langlands.Shimura.RestrictedSplitLevelTowerCohomology

variable {F : Type} [Field F] [NumberField F]

/-- The localization of the integers of `F` at `v`, realized as a subring of `F`. -/
abbrev CMIntegralTraitRing (v : Global.FinitePlace F) := ↥(v.valuationSubringAtPrime F)

/-- Generic point of the local arithmetic trait, with its specified field `F`. -/
def cmIntegralTraitGenericMap (v : Global.FinitePlace F) :
    Spec (.of F) ⟶ Spec (.of (CMIntegralTraitRing v)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (CMIntegralTraitRing v) F))

/-- Closed point of the local arithmetic trait, with its actual residue field. -/
def cmIntegralTraitClosedMap (v : Global.FinitePlace F) :
    Spec (.of (IsLocalRing.ResidueField (CMIntegralTraitRing v))) ⟶
      Spec (.of (CMIntegralTraitRing v)) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue (CMIntegralTraitRing v)))

variable {E A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L] [IsQuadraticExtension ℚ L]
  [Algebra L F] {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})
  (q : CMRepresentabilityStatement D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor)
  (p : ℕ) [Fact p.Prime]
  (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints p)ᵐᵒᵖ)

local notation "hp0" => (Fact.out : p.Prime).ne_zero
local notation "tameLevels" => (cmPrimeToProperty D p hp0 K₀).FullSubcategory
local notation "chosen" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- The actual arithmetic Harris tower with the level at `p` held fixed. -/
abbrev cmHarrisTameOverTower : tameLevels ⥤ Over (Spec (.of F)) :=
  awayFunctor (cmPrimeToSplit D p hp0) D.rationalInvolution.LevelSufficientlySmall K₀ ⋙
    representedCMOverTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability compatibility
      h htor chosen

local notation "harrisTame" => cmHarrisTameOverTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q p K₀

/-- Scheme-level input for hyperspecial good reduction. The generic fibre identification is a
natural isomorphism on the actual prime-to-`p` transporter category, not just a levelwise
identification of objects. In particular it intertwines both arrows of every span indexed by
arrows of that category. No representability or coefficient extension is part of this definition. -/
structure CMHarrisTameIntegralTower (v : FinitePlacesAbove F (rationalPrimePlace p)) where
  tower : tameLevels ⥤ Over (Spec (.of (CMIntegralTraitRing v.1)))
  genericIso : tower ⋙ Over.pullback (cmIntegralTraitGenericMap v.1) ≅ harrisTame
  smooth : ∀ U, SmoothOfRelativeDimension (n - 1) (tower.obj U).hom
  projective : ∀ U, IsHProjective (tower.obj U).hom
  finite : ∀ ⦃U V⦄ (g : U ⟶ V), IsFinite (tower.map g).left
  etale : ∀ ⦃U V⦄ (g : U ⟶ V), Etale (tower.map g).left

variable {v : FinitePlacesAbove F (rationalPrimePlace p)}
  (I : CMHarrisTameIntegralTower D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q p K₀ v)

/-- The actual special fibre tower over the residue field. -/
abbrev CMHarrisTameIntegralTower.specialTower :
    tameLevels ⥤ Over (Spec (.of (IsLocalRing.ResidueField (CMIntegralTraitRing v.1)))) :=
  I.tower ⋙ Over.pullback (cmIntegralTraitClosedMap v.1)

/-- On underlying generic-fibre schemes the comparison square for every transporter arrow. -/
theorem CMHarrisTameIntegralTower.genericIso_naturality {U V : tameLevels} (g : U ⟶ V) :
    ((I.tower ⋙ Over.pullback (cmIntegralTraitGenericMap v.1)).map g).left ≫
        (I.genericIso.hom.app V).left =
      (I.genericIso.hom.app U).left ≫ ((harrisTame).map g).left :=
  congrArg (fun m => m.left) (I.genericIso.hom.naturality g)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
