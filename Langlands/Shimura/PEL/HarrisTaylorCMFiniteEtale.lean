import Langlands.Shimura.PEL.HarrisTaylorCMNormalEtale
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Proper CM transitions and their finite-etale realizations -/

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


variable {L : Type} [Field L] [NumberField L] [IsCMField L]
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


local notation "schemes" => representedCMSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "quotientAction" => representedCMNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "projection" => representedCMNormalProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

/-- The existing projective-space witness proves properness of each represented level. -/
instance representedCMLevel_isProper (U : SmallCMLevel D) :
    IsProper (R U).base.obj.hom := by
  obtain ⟨m, i, hi, he⟩ := (R U).projective
  have : IsClosedImmersion i := hi
  rw [← he]
  infer_instance

/-- Every original transporter transition is proper, by its equation over the CM field. -/
instance representedCMSchemeTower_map_isProper {U V : SmallCMLevel D} (k : U ⟶ V) :
    IsProper ((schemes R).map k) := by
  have : IsProper ((schemes R).map k ≫ (R V).base.obj.hom) := by
    rw [representedCMSchemeTower_over]
    infer_instance
  exact IsProper.of_comp ((schemes R).map k) (R V).base.obj.hom

/-- An etale original transition is finite; no separate finiteness premise is needed. -/
instance representedCMSchemeTower_map_isFinite {U V : SmallCMLevel D} (k : U ⟶ V)
    [Etale ((schemes R).map k)] : IsFinite ((schemes R).map k) := by
  have : LocallyQuasiFinite ((schemes R).map k) :=
    Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale _
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- An original etale transition as an object of the existing finite-etale category. -/
def representedCMFiniteEtaleTransition {U V : SmallCMLevel D} (k : U ⟶ V)
    [Etale ((schemes R).map k)] : Cover ((schemes R).obj V) :=
  cover ((schemes R).map k)

local notation "finiteTransition" => representedCMFiniteEtaleTransition D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

@[simp] theorem representedCMFiniteEtaleTransition_left {U V : SmallCMLevel D}
    (k : U ⟶ V) [Etale ((schemes R).map k)] :
    (finiteTransition R k).obj.left = (schemes R).obj U := rfl

@[simp] theorem representedCMFiniteEtaleTransition_hom {U V : SmallCMLevel D}
    (k : U ⟶ V) [Etale ((schemes R).map k)] :
    (finiteTransition R k).obj.hom = (schemes R).map k := rfl

variable (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

/-- Original normal forgetting is proper even before etaleness is known. -/
instance representedCMNormalProjection_isProper : IsProper (projection R U V hVU) :=
  representedCMSchemeTower_map_isProper D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R (smallCMInclusion D hVU)

/-- Etaleness alone discharges finiteness for the original normal projection. -/
instance representedCMNormalProjection_isFinite [Etale (projection R U V hVU)] :
    IsFinite (projection R U V hVU) := by
  have : LocallyQuasiFinite (projection R U V hVU) :=
    Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale _
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- Every original residual graph is a closed immersion into the actual kernel pair. -/
instance representedCMNormalGraph_isClosedImmersion (g : SmallCMResidualGroup D U V) :
    IsClosedImmersion (representedCMNormalGraph D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R U V hVU g) := by
  let graphMap := representedCMNormalGraph D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R U V hVU g
  have : IsClosedImmersion (graphMap ≫ pullback.fst (projection R U V hVU)
      (projection R U V hVU)) := by
    rw [representedCMNormalGraph_fst]
    infer_instance
  exact IsClosedImmersion.of_comp graphMap (pullback.fst _ _)

/-- The original residual action in the actual finite-etale cover category. -/
def representedCMNormalFiniteEtaleAction [Etale (projection R U V hVU)] :
    Action (Cover ((schemes R).obj U)) (SmallCMResidualGroup D U V) where
  V := cover (projection R U V hVU)
  ρ :=
    { toFun := fun g => ObjectProperty.homMk (Over.homMk ((quotientAction R U V hVU).ρ g)
        (representedCMNormalProjection_invariant D C preservation composition
          unitCoherence associativity comparison symmetry stability square universality
          dualityNaturality polarizationStability compatibility h htor R U V hVU g))
      map_one' := by
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        exact (quotientAction R U V hVU).ρ.map_one
      map_mul' := fun g g' => by
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        exact (quotientAction R U V hVU).ρ.map_mul g g' }

local notation "finiteAction" => representedCMNormalFiniteEtaleAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

@[simp] theorem representedCMNormalFiniteEtaleAction_left [Etale (projection R U V hVU)] :
    (finiteAction R U V hVU).V.obj.left = (schemes R).obj V := rfl

@[simp] theorem representedCMNormalFiniteEtaleAction_hom [Etale (projection R U V hVU)] :
    (finiteAction R U V hVU).V.obj.hom = projection R U V hVU := rfl

@[simp] theorem representedCMNormalFiniteEtaleAction_ρ_left
    [Etale (projection R U V hVU)] (g : SmallCMResidualGroup D U V) :
    ((finiteAction R U V hVU).ρ g).hom.left = (quotientAction R U V hVU).ρ g := rfl

/-- The existing etale torsor adapter needs no separate finiteness hypothesis. -/
theorem representedCMNormalEtaleAction_isFiniteGeometricTorsor_of_projective
    [Etale (projection R U V hVU)]
    [IsIso (representedCMNormalKernelComparison D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R U V hVU)]
    (hsurj : Function.Surjective (projection R U V hVU)) :
    Coefficients.IsFiniteGeometricTorsor ((schemes R).obj U)
      (representedCMNormalEtaleAction D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor R U V hVU) :=
  representedCMNormalEtaleAction_isFiniteGeometricTorsor D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R U V hVU hsurj

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

local notation "chosen" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- The finite-etale action from the exact CM representability target and original etaleness. -/
def cmNormalFiniteEtaleAction [Etale (projection chosen U V hVU)] :=
  finiteAction chosen U V hVU

/-- For the exact chosen witnesses, projectivity discharges the finiteness
premise of the existing small-etale torsor adapter. -/
theorem cmNormalEtaleAction_isFiniteGeometricTorsor_of_projective
    [Etale (projection chosen U V hVU)]
    [IsIso (representedCMNormalKernelComparison D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor chosen U V hVU)]
    (hsurj : Function.Surjective (projection chosen U V hVU)) :
    Coefficients.IsFiniteGeometricTorsor ((schemes chosen).obj U)
      (cmNormalEtaleAction D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U V hVU q) :=
  representedCMNormalEtaleAction_isFiniteGeometricTorsor_of_projective D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    chosen U V hVU hsurj

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
