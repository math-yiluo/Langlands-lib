import Langlands.Representation.Geometric.RepresentedGeometricLemmaCompactNaturality
import Langlands.Representation.Induction.CompactNormalizationEvaluation

/-! # Evaluation of the original normalized compact-orbit comparison -/

noncomputable section

universe u v

set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Induction

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance compactEvaluationAmbientTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

local notation "MI" => pointImage (lQ ≫ q)
local notation "Kt" => geometricTargetIntersection MI (pointImage p) z⁻¹
local notation "Ki" => Subgroup.subgroupOf Kt MI
local notation "flat" => subgroupOfContinuousEquiv (inf_le_left : Kt ≤ MI)
local notation "H" => Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹
local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
local notation "π" => IsSemidirectDecomposition.projection dQ
local notation "sQ" => Subgroup.inclusion (IsSemidirectDecomposition.levi_le dQ)
local notation "S" => compactComparisonSaturation D
local notation "hker" => projectionKernel_le_compactComparisonSaturation D
local notation "K0" => Subgroup.comap sQ S
local notation "rS" => splitStagesRetraction π sQ
  (fun m => IsSemidirectDecomposition.projection_levi dQ m) S hker
local notation "sS" => MonoidHom.subgroupComap sQ S
local notation "HS" => Subgroup.subgroupOf H S
local notation "I" => Subgroup.comap (Subgroup.subtype (MonoidHom.ker rS)) HS
local notation "hSI" => compactComparisonSaturation_section_mem_stabilizer D
local notation "hH" => Geometric.isClosed_orbitStabilizer
  (pointImage p) (pointImage q) z⁻¹ (isClosed_pointImage p hp.isClosedSubgroup)
local notation "hHSc" => IsClosed.preimage
  (continuous_subtype_val : Continuous (Subgroup.subtype S)) hH

local instance compactEvaluationKernelLocallyCompact :
    LocallyCompactSpace (MonoidHom.ker rS) :=
  representedNestedKernelLocallyCompactSpace q lQ rQ hq hrQ hmulQ S hker
local instance compactEvaluationKernelMeasurable : MeasurableSpace (MonoidHom.ker rS) :=
  borel _
local instance compactEvaluationKernelBorel : BorelSpace (MonoidHom.ker rS) := ⟨rfl⟩
local instance compactEvaluationIntersectionMeasurable : MeasurableSpace I := borel _
local instance compactEvaluationIntersectionBorel : BorelSpace I := ⟨rfl⟩

variable (A : letI := leviPointTopology l hl; SmoothRep.{0,u,v} ℂ (rationalPoints M))

local notation "σ" => Rep.ρ
  (Functor.obj (stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z) A)

namespace DynamicRealization

variable {D} (R : D.DynamicRealization)

local notation "hHS" => stabilizer_le_compactComparisonSaturation R
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHS)
local notation "κ" => Langlands.twist
  (Jacquet.complexCharacter (splitKernelHaarRatio rS sS HS hSI hHSc))
  (splitKernelCoefficientAction rS sS HS hSI (MonoidHom.comp σ φ))

set_option maxHeartbeats 100000 in
/-- Actual values of the directly assembled natural comparison, together with
its evaluation identity and the original character-times-integral formula. -/
def compactInducedNaturalEvaluation :=
  letI := leviPointTopology l hl
  CompactNormalizationTransport.normalizedTransportEvaluation
    D.compactComparisonSaturation_comap_section _ _
    (D.targetIntersectionCoefficientInLevi A) D.compactOuterInverseHalfAmbient
    ((R.compactOrbitIntegralAbstractFamily).val
      (compactSmoothStabilizerCoefficient (p := p) (l := l) (r := r)
        (hp := hp) (hr := hr) (hl := hl) (hmul := hmul) (q := q) (z := z) A))
    (restrictAlongEquiv (flat).toMonoidHom (R.compactNormalizedCoefficientEquiv A))

/-- The actual value function carried by the proved evaluation package. -/
def compactInducedNaturalValue :=
  letI := leviPointTopology l hl
  (R.compactInducedNaturalEvaluation A).val

end DynamicRealization

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
