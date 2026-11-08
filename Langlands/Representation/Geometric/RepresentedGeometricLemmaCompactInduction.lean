import Langlands.Representation.Geometric.RepresentedGeometricLemmaCompactNormalization
import Langlands.Representation.Geometric.RepresentedGeometricLemmaTargetInduction
import Langlands.Representation.Induction.CompactNormalizationTransport

/-! # Normalized compact induction from the original represented orbit -/

noncomputable section

universe u v w

set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Induction

private theorem compactInducedSubgroupCongr_eval
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    {H K : Subgroup A} (h : H = K) (σ : Representation ℂ H V)
    (F : CompactFunctions H σ) (a : A) :
    eval K (σ.comp (MulEquiv.subgroupCongr h).symm.toMonoidHom)
      (CompactNormalizationTransport.subgroupCongr h σ F).val a = eval H σ F.val a := by
  subst K
  rfl

private theorem compactInducedSubgroupEquiv_eval
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W]
    {H K : Subgroup A} (h : H = K)
    (σ : Representation ℂ H V) (τ : Representation ℂ K W)
    (e : Representation.Equiv (σ.comp (MulEquiv.subgroupCongr h).symm.toMonoidHom) τ)
    (F : CompactFunctions H σ) (a : A) :
    eval K τ (CompactNormalizationTransport.subgroupTransport h σ τ e F).val a =
      e (eval H σ F.val a) := by
  subst K
  rfl

end Langlands.Induction

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Induction

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance compactInductionAmbientTopology :
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

local instance compactOrbitKernelLocallyCompact :
    LocallyCompactSpace (MonoidHom.ker rS) :=
  representedNestedKernelLocallyCompactSpace q lQ rQ hq hrQ hmulQ S hker
local instance compactOrbitKernelMeasurable : MeasurableSpace (MonoidHom.ker rS) :=
  borel _
local instance compactOrbitKernelBorel : BorelSpace (MonoidHom.ker rS) := ⟨rfl⟩
local instance compactOrbitIntersectionMeasurable : MeasurableSpace I := borel _
local instance compactOrbitIntersectionBorel : BorelSpace I := ⟨rfl⟩

variable (A : letI := leviPointTopology l hl; SmoothRep.{0,u,v} ℂ (rationalPoints M))

local notation "σ" => Rep.ρ
  (Functor.obj (stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z) A)

/-- The original stabilizer coefficient, with its proved smoothness. -/
abbrev compactSmoothStabilizerCoefficient :
    letI := leviPointTopology l hl
    SmoothRep.{0,u,v} ℂ H := by
  letI := leviPointTopology l hl
  exact ⟨(stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A,
    isSmooth_stabilizerTwistedCoefficientFunctor_obj p l r hp hr hl hmul q z A⟩

namespace DynamicRealization

variable {D} (R : D.DynamicRealization)

local notation "hHS" => stabilizer_le_compactComparisonSaturation R
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHS)
local notation "κ" => Langlands.twist
  (Jacquet.complexCharacter (splitKernelHaarRatio rS sS HS hSI hHSc))
  (splitKernelCoefficientAction rS sS HS hSI (MonoidHom.comp σ φ))

set_option maxHeartbeats 100000 in
/-- The component of the common chosen natural relative-integral family,
on the original smooth stabilizer coefficient. -/
def compactOrbitIntegralComponent :
    letI := leviPointTopology l hl
    Representation.Equiv
      (((compactInduced H σ).toCoinvariants (π).ker).comp sQ)
      (compactInduced K0 κ) := by
  letI := leviPointTopology l hl
  exact (D.orbitCompactComparison R).val
    (compactSmoothStabilizerCoefficient (p := p) (l := l) (r := r)
      (hp := hp) (hr := hr) (hl := hl) (hmul := hmul) (q := q) (z := z) A)

set_option maxHeartbeats 100000 in
/-- Original target-kernel coinvariants with original target inverse-half
normalization are actual compact induction of the normalized source coefficient. -/
def compactInducedNormalizedEquiv :
    letI := leviPointTopology l hl
    (Langlands.twist D.compactOuterInverseHalfAmbient.toMonoidHom
      (((compactInduced H σ).toCoinvariants (π).ker).comp sQ)).Equiv
      (compactInduced Ki (D.targetIntersectionCoefficientInLevi A)) := by
  letI := leviPointTopology l hl
  let E0 := Langlands.twistEquiv D.compactOuterInverseHalfAmbient.toMonoidHom
    (R.compactOrbitIntegralComponent A)
  let E1 := compactInductionTwistEquiv K0 D.compactOuterInverseHalfAmbient κ
  let E2 := Induction.CompactNormalizationTransport.subgroupTransport
    D.compactComparisonSaturation_comap_section
    (Langlands.twist (D.compactOuterInverseHalfAmbient.toMonoidHom.comp (K0).subtype) κ)
    (D.targetIntersectionCoefficientInLevi A)
    (restrictAlongEquiv (flat).toMonoidHom (R.compactNormalizedCoefficientEquiv A))
  refine E0.trans ?_
  refine E1.trans ?_
  exact E2

end DynamicRealization

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
