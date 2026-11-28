import Langlands.Shimura.PEL.HarrisTaylorCMAnalyticTower
import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients
import Langlands.Global.FiniteCompletionUnramified
import Langlands.Geometry.Analytic.LocalizedGroundFieldExtension

/-! # The represented CM tower over the completed unramified local field -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
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

open Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
  (localizedFunctor localizedProjection)
open Langlands.Global.FiniteCompletion
  (CompletedUnramified completedUnramifiedArithmeticFrobenius unramifiedBaseNormedField
    unramifiedBase_ultrametric unramifiedBase_complete completedUnramifiedNormedAlgebra)

variable (v : Global.FinitePlace F)

local notation "Kloc" => Global.FiniteCompletion F v
local notation "Knr" => CompletedUnramified v
local notation "Knorm" => unramifiedBaseNormedField v

private abbrev unramifiedBaseAnalyticCategory :=
  @LocalizedCategory.{0, 0, 0} Kloc (Knorm).toNormedField
  (unramifiedBase_ultrametric v) (unramifiedBase_complete v)

/-- The actual represented CM scheme tower over the completed unramified extension
of the finite-place completion. -/
abbrev cmUnramifiedOverTower : SmallCMLevel D ⥤ Over (Spec (.of (CompletedUnramified v))) :=
  cmFieldOverTower D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality dualityNaturality polarizationStability compatibility
    h htor q (CompletedUnramified v)

/-- Base change to the unramified field is the composite of base change to the finite-place
completion and base change along its embedding into the unramified field. -/
def cmUnramifiedOverTowerBaseChangeIso :
    cmUnramifiedOverTower D C preservation composition unitCoherence associativity comparison
        symmetry stability square universality dualityNaturality polarizationStability
        compatibility h htor q v ≅
      cmLocalOverTower D C preservation composition unitCoherence associativity comparison
        symmetry stability square universality dualityNaturality polarizationStability
        compatibility h htor q v ⋙
          Over.pullback (Spec.algebraMap (Global.FiniteCompletion F v) (CompletedUnramified v)) := by
  let K := Global.FiniteCompletion F v
  let M := CompletedUnramified v
  let a := cmFieldExtensionMap (F := F) K
  let b := Spec.algebraMap K M
  have eq : b ≫ a = cmFieldExtensionMap (F := F) M := by
    change Spec.map (CommRingCat.ofHom (algebraMap K M)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap F K)) =
      Spec.map (CommRingCat.ofHom (algebraMap F M))
    rw [← Spec.map_comp]
    rfl
  let chosen := chosenCMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q
  let T := representedCMOverTower D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality dualityNaturality polarizationStability compatibility h htor chosen
  let j := eqToIso (congrArg (fun g => Over.pullback g) eq.symm) ≪≫ Over.pullbackComp b a
  exact Functor.isoWhiskerLeft T j ≪≫ (Functor.associator T (Over.pullback a) (Over.pullback b)).symm

/-- The actual analytic spaces of the unramified tower, including the transporter maps. -/
abbrev cmUnramifiedAnalyticTower :
    SmallCMLevel D ⥤ LocalizedCategory.{0, 0, 0} (K := CompletedUnramified v) :=
  cmFieldAnalyticTower D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality dualityNaturality polarizationStability compatibility
    h htor q (CompletedUnramified v)

/-- Analytification over the finite-place completion with the precise base norm of the
completed unramified extension. -/
abbrev cmUnramifiedBaseAnalyticTower : SmallCMLevel D ⥤ unramifiedBaseAnalyticCategory v :=
  letI := unramifiedBaseNormedField v
  letI := unramifiedBase_ultrametric v
  letI := unramifiedBase_complete v
  cmFieldAnalyticTower D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q Kloc

local notation "localTower" => cmUnramifiedBaseAnalyticTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q v

private abbrev analyticFieldExtension :
    unramifiedBaseAnalyticCategory v ⥤ LocalizedCategory.{0, 0, 0} (K := Knr) :=
  @localizedFunctor.{0, 0, 0, 0} Kloc (Knorm).toNormedField
    (unramifiedBase_ultrametric v) (unramifiedBase_complete v) Knr _ _ _
    (completedUnramifiedNormedAlgebra v)

/-- The tower obtained by applying the actual analytic ground-field extension to
the represented analytic tower over the local base. -/
abbrev cmUnramifiedScalarExtendedAnalyticTower :
    SmallCMLevel D ⥤ LocalizedCategory.{0, 0, 0} (K := Knr) :=
  localTower ⋙ analyticFieldExtension v

/-- Analytic scalar extension gives a natural continuous projection onto the local
analytic point tower, including along Hecke transporters. -/
def cmUnramifiedScalarExtendedProjection :
    cmUnramifiedScalarExtendedAnalyticTower D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality polarizationStability
        compatibility h htor q v ⋙ localizedSpaceFunctor ⟶
      localTower ⋙ @localizedSpaceFunctor.{0, 0, 0} Kloc (Knorm).toNormedField
        (unramifiedBase_ultrametric v) (unramifiedBase_complete v) := by
  let π := @localizedProjection.{0, 0, 0, 0} Kloc (Knorm).toNormedField
    (unramifiedBase_ultrametric v) (unramifiedBase_complete v) Knr _ _ _
    (completedUnramifiedNormedAlgebra v)
  refine { app := fun U => TopCat.uliftFunctor.{0, 0}.preimage (π.app ((localTower).obj U))
           naturality := ?_ }
  intro U V k
  apply TopCat.uliftFunctor.{0, 0}.map_injective
  simp only [Functor.map_comp, Functor.map_preimage]
  exact π.naturality ((localTower).map k)

local notation "cmSchemes" => cmFieldSchemeTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q (CompletedUnramified v)
local notation "arithmeticStructure" => cmSmallLevelArithmeticStructure D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q
local notation "genericTower" => RestrictedLevelTowerGalois.baseChangeTower F (CompletedUnramified v)
  arithmeticStructure

/-- The two definitions of the base-changed scheme tower are canonically isomorphic by
identities on the scheme fibre products. -/
def cmUnramifiedSchemeBaseChangeIso : genericTower ≅ cmSchemes :=
  NatIso.ofComponents (fun U => Iso.refl _) (fun {U V} k => by
    apply pullback.hom_ext <;>
      simp [RestrictedLevelTowerGalois.baseChangeTower, cmFieldSchemeTower, cmFieldOverTower,
        cmFieldExtensionMap, cmSmallLevelArithmeticStructure, cmSchemeTower, representedCMSchemeTower])

/-- The tower automorphism from an automorphism of the unramified coefficient field
fixing the local base. At each level it acts on the second factor of the scheme pullback. -/
def cmUnramifiedSchemeAut (σ : CompletedUnramified v ≃ₐ[Global.FiniteCompletion F v]
    CompletedUnramified v) : cmSchemes ≅ cmSchemes :=
  let e := cmUnramifiedSchemeBaseChangeIso D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q v
  e.symm ≪≫ RestrictedLevelTowerGalois.towerGaloisAut arithmeticStructure (σ.restrictScalars F) ≪≫ e

/-- The natural arithmetic Frobenius automorphism of the underlying unramified scheme tower. -/
def cmUnramifiedSchemeFrobenius : cmSchemes ≅ cmSchemes :=
  cmUnramifiedSchemeAut D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality dualityNaturality polarizationStability compatibility
    h htor q v (completedUnramifiedArithmeticFrobenius v)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
