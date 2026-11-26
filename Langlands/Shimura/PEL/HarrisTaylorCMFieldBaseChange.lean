import Langlands.Shimura.PEL.HarrisTaylorCMSchemeLevels

/-! # Field base change of the represented CM level tower -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
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

open Langlands.AlgebraicGeometry

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)
  (K : Type) [Field K] [Algebra F K]

local notation "chosen" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "overTower" => representedCMOverTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor chosen
local notation "schemes" => cmSchemeTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q

/-- The morphism of field spectra associated to the chosen scalar embedding. -/
def cmFieldExtensionMap : Spec (.of K) ⟶ Spec (.of F) :=
  Scheme.Spec.map (CommRingCat.ofHom (algebraMap F K)).op

local notation "specMap" => cmFieldExtensionMap (F := F) K

/-- The represented CM tower after field base change, with its structure maps to `Spec K`. -/
def cmFieldOverTower : SmallCMLevel D ⥤ Over (Spec (.of K)) :=
  overTower ⋙ Over.pullback specMap

local notation "fieldOver" => cmFieldOverTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q K

/-- The underlying schemes and level maps of the field base change. -/
def cmFieldSchemeTower : SmallCMLevel D ⥤ Scheme :=
  fieldOver ⋙ Over.forget (Spec (.of K))

local notation "fieldSchemes" => cmFieldSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q K

/-- The first projections of the field pullbacks assemble across the entire transporter tower. -/
def cmFieldProjection : fieldSchemes ⟶ schemes where
  app U := pullback.fst ((overTower).obj U).hom specMap
  naturality {U V} k := by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    simp [cmSchemeTower, representedCMSchemeTower]

local notation "projection" => cmFieldProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q K

/-- Each level is the scheme pullback along the scalar embedding. -/
theorem cmFieldSchemeTower_isPullback (U : SmallCMLevel D) :
    IsPullback ((projection).app U) ((fieldOver).obj U).hom ((overTower).obj U).hom specMap :=
  IsPullback.of_hasPullback _ _

/-- Each transporter map is the base change of the original represented map. -/
theorem cmFieldSchemeTower_map_isPullback {U V : SmallCMLevel D} (k : V ⟶ U) :
    IsPullback ((projection).app V) ((fieldSchemes).map k) ((schemes).map k) ((projection).app U) := by
  refine IsPullback.of_bot ?_ ((projection).naturality k).symm
    (cmFieldSchemeTower_isPullback D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q K U)
  change IsPullback _ (((fieldOver).map k).left ≫ ((fieldOver).obj U).hom)
    (((overTower).map k).left ≫ ((overTower).obj U).hom) _
  simpa only [Over.w] using
    (cmFieldSchemeTower_isPullback D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q K V)

/-- Smoothness of the represented CM levels is preserved by this base change. -/
instance cmFieldOverTower_smooth (U : SmallCMLevel D) : Smooth ((fieldOver).obj U).hom := by
  change Smooth (pullback.snd ((overTower).obj U).hom specMap)
  infer_instance

/-- The CM scheme tower over the canonical completion of the CM base field `F` at `v`. -/
abbrev cmLocalOverTower (v : Global.FinitePlace F) :
    SmallCMLevel D ⥤ Over (Spec (.of (Global.FiniteCompletion F v))) :=
  cmFieldOverTower D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q (Global.FiniteCompletion F v)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
