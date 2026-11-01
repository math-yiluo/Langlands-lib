import Langlands.Shimura.PEL.HarrisTaylorCMFiniteEtale
import Langlands.Shimura.PEL.HarrisTaylorCMKernelSurjectivity
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Finite original CM normal projections from residual point orbits -/

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
  (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

local notation "copies" => representedCMNormalCopies D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelPair" => representedCMNormalKernelPair D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelComparison" => representedCMNormalKernelComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "graph" => representedCMNormalGraph D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The original residual orbit map lands in the exact underlying point fiber. -/
def representedCMNormalPointFiberMap (x : (schemes R).obj V)
    (g : SmallCMResidualGroup D U V) :
    {z : (schemes R).obj V // projection R U V hVU z = projection R U V hVU x} :=
  ⟨(Scheme.Hom.toLRSHom ((quotientAction R U V hVU).ρ g)).base x, by
    change ((quotientAction R U V hVU).ρ g ≫ projection R U V hVU) x = _
    rw [representedCMNormalProjection_invariant]
    rfl⟩

local notation "pointFiberMap" => representedCMNormalPointFiberMap D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

@[simp] theorem representedCMNormalPointFiberMap_val
    (x : (schemes R).obj V) (g : SmallCMResidualGroup D U V) :
    (pointFiberMap R U V hVU x g).val =
      (Scheme.Hom.toLRSHom ((quotientAction R U V hVU).ρ g)).base x := rfl

/-- Same-fiber underlying scheme points differ by an original residual translate.
This conclusion uses neither coarse rigidity nor etaleness. -/
theorem representedCMNormalPoint_exists_translate
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (x y : (schemes R).obj V)
    (hxy : projection R U V hVU x = projection R U V hVU y) :
    ∃ g : SmallCMResidualGroup D U V,
      (Scheme.Hom.toLRSHom ((quotientAction R U V hVU).ρ g)).base x = y := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := projection R U V hVU) (g := projection R U V hVU) x y hxy
  obtain ⟨w, hw⟩ := representedCMNormalKernelComparison_surjective D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry z
  obtain ⟨⟨g, t⟩, ht⟩ :=
    (AlgebraicGeometry.sigmaMk
      (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V)).surjective w
  rw [AlgebraicGeometry.sigmaMk_mk] at ht
  have hgraph : graph R U V hVU g t = z := by
    calc
      graph R U V hVU g t =
          (Sigma.ι (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V) g ≫
            kernelComparison R U V hVU) t := by
        rw [representedCMNormalKernelComparison_ι]
      _ = kernelComparison R U V hVU w := by
        exact congrArg (fun s => kernelComparison R U V hVU s) ht
      _ = z := hw
  have htx : t = x := by
    calc
      t = (graph R U V hVU g ≫
          pullback.fst (projection R U V hVU) (projection R U V hVU)) t := by
        rw [representedCMNormalGraph_fst]
        rfl
      _ = pullback.fst (projection R U V hVU) (projection R U V hVU) z := by
        exact congrArg
          (fun s => pullback.fst (projection R U V hVU) (projection R U V hVU) s)
          hgraph
      _ = x := hz₁
  refine ⟨g, ?_⟩
  calc
    (Scheme.Hom.toLRSHom ((quotientAction R U V hVU).ρ g)).base x =
        (Scheme.Hom.toLRSHom ((quotientAction R U V hVU).ρ g)).base t :=
      congrArg
        (fun s => (Scheme.Hom.toLRSHom ((quotientAction R U V hVU).ρ g)).base s) htx.symm
    _ = (graph R U V hVU g ≫
        pullback.snd (projection R U V hVU) (projection R U V hVU)) t := by
      rw [representedCMNormalGraph_snd]
      rfl
    _ = pullback.snd (projection R U V hVU) (projection R U V hVU) z := by
      exact congrArg
        (fun s => pullback.snd (projection R U V hVU) (projection R U V hVU) s)
        hgraph
    _ = y := hz₂

/-- The constructed original residual orbit map surjects onto the point fiber. -/
theorem representedCMNormalPointFiberMap_surjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (x : (schemes R).obj V) :
    Function.Surjective (pointFiberMap R U V hVU x) := by
  intro y
  obtain ⟨g, hg⟩ := representedCMNormalPoint_exists_translate D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry x y.val y.property.symm
  exact ⟨g, Subtype.ext hg⟩

/-- Every underlying fiber of original normal forgetting is finite. -/
theorem representedCMNormalProjection_finite_preimage_singleton
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (y : (schemes R).obj U) :
    (projection R U V hVU ⁻¹' {y}).Finite := by
  classical
  have : Finite (SmallCMResidualGroup D U V) := smallCMResidualGroup_finite D U V
  rcases Set.eq_empty_or_nonempty (projection R U V hVU ⁻¹' {y}) with hy | ⟨x, hx⟩
  · rw [hy]
    exact Set.finite_empty
  · apply (Set.finite_range (fun g : SmallCMResidualGroup D U V =>
      (Scheme.Hom.toLRSHom ((quotientAction R U V hVU).ρ g)).base x)).subset
    intro z hz
    have hpx : projection R U V hVU x = y := hx
    have hpz : projection R U V hVU z = y := hz
    exact representedCMNormalPoint_exists_translate D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry x z (hpx.trans hpz.symm)

/-- Finite fibers and original properness prove local quasi-finiteness. -/
theorem representedCMNormalProjection_locallyQuasiFinite_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    LocallyQuasiFinite (projection R U V hVU) :=
  LocallyQuasiFinite.of_finite_preimage_singleton _
    (representedCMNormalProjection_finite_preimage_singleton D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry)

/-- Original normal forgetting is finite without an etaleness premise. -/
theorem representedCMNormalProjection_isFinite_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    IsFinite (projection R U V hVU) := by
  have : LocallyQuasiFinite (projection R U V hVU) :=
    representedCMNormalProjection_locallyQuasiFinite_of_dualGeometry D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

local notation "chosenReps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenSchemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenAction" => cmNormalQuotientAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

/-- The point-fiber map for precisely the chosen representations defining `cmSchemeTower`. -/
def cmNormalPointFiberMap (x : (chosenSchemes q).obj V)
    (g : SmallCMResidualGroup D U V) :
    {z : (chosenSchemes q).obj V //
      (chosenSchemes q).map (smallCMInclusion D hVU) z =
        (chosenSchemes q).map (smallCMInclusion D hVU) x} :=
  pointFiberMap (chosenReps q) U V hVU x g

local notation "chosenPointFiberMap" => cmNormalPointFiberMap D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU q

@[simp] theorem cmNormalPointFiberMap_val
    (x : (chosenSchemes q).obj V) (g : SmallCMResidualGroup D U V) :
    (chosenPointFiberMap x g).val =
      (Scheme.Hom.toLRSHom ((chosenAction q).ρ g)).base x := rfl

/-- Same-fiber points in the exact chosen tower are related by its original action. -/
theorem cmNormalPoint_exists_translate
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (x y : (chosenSchemes q).obj V)
    (hxy : (chosenSchemes q).map (smallCMInclusion D hVU) x =
      (chosenSchemes q).map (smallCMInclusion D hVU) y) :
    ∃ g : SmallCMResidualGroup D U V,
      (Scheme.Hom.toLRSHom ((chosenAction q).ρ g)).base x = y :=
  representedCMNormalPoint_exists_translate D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry x y hxy

/-- The exact chosen point-fiber map is surjective. -/
theorem cmNormalPointFiberMap_surjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (x : (chosenSchemes q).obj V) :
    Function.Surjective (chosenPointFiberMap x) :=
  representedCMNormalPointFiberMap_surjective D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry x

/-- Every underlying point fiber of the exact chosen forgetting map is finite. -/
theorem cmNormalProjection_finite_preimage_singleton
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (y : (chosenSchemes q).obj U) :
    ((chosenSchemes q).map (smallCMInclusion D hVU) ⁻¹' {y}).Finite :=
  representedCMNormalProjection_finite_preimage_singleton D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry y

/-- The original chosen forgetting map is locally quasi-finite. -/
theorem cmNormalProjection_locallyQuasiFinite_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    LocallyQuasiFinite ((chosenSchemes q).map (smallCMInclusion D hVU)) :=
  representedCMNormalProjection_locallyQuasiFinite_of_dualGeometry D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry

/-- The original chosen forgetting map is finite without etaleness or rigidity. -/
theorem cmNormalProjection_isFinite_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    IsFinite ((chosenSchemes q).map (smallCMInclusion D hVU)) :=
  representedCMNormalProjection_isFinite_of_dualGeometry D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
