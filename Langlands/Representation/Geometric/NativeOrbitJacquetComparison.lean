import Langlands.Representation.Geometric.NativeOrbitEndpointAdmissibility
import Langlands.Representation.Induction.CoefficientSplitStagesCovered
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof

/-! Native compact orbit Jacquet comparison on the original represented groups. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 20000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Induction

universe u uR uV

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance nativeOrbitJacquetPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}
  {B : Type uR} [CommRing B] [Algebra ℂ B]
  {V : Type uV} [AddCommGroup V] [Module B V]
  [Module ℂ V] [IsScalarTower ℂ B V]

local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
local notation "π" => IsSemidirectDecomposition.projection dQ
local notation "s" => Subgroup.inclusion (IsSemidirectDecomposition.levi_le dQ)
local notation "hrs" => (fun m => IsSemidirectDecomposition.projection_levi dQ m)

set_option maxHeartbeats 80000 in
/-- The original represented projection kernel has an actual compact-open
cover, by removing the redundant top stages subgroup from the radical cover. -/
theorem representedProjectionKernel_compactOpenCover (x : (π).ker) :
    ∃ K : OpenSubgroup (π).ker, IsCompact (K : Set (π).ker) ∧ x ∈ K := by
  let e := splitStagesKernelContinuousEquiv π s hrs ⊤ le_top
  obtain ⟨K, hK, hx⟩ :=
    representedNestedKernel_compactOpenCover q lQ rQ hq hrQ hmulQ ⊤ le_top (e.symm x)
  exact ⟨K.comap e.symm.toMonoidHom e.symm.continuous,
    e.symm.toHomeomorph.isCompact_preimage.mpr hK, hx⟩

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

local notation "H" => Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹
local notation "S" => D.compactComparisonSaturation
local notation "K" => Subgroup.comap s S
local notation "hSI" => D.compactComparisonSaturation_section_mem_stabilizer
local notation "hH" => Geometric.isClosed_orbitStabilizer
  (pointImage p) (pointImage q) z⁻¹ (isClosed_pointImage p hp.isClosedSubgroup)
local notation "rS" => splitStagesRetraction π s hrs
  S D.projectionKernel_le_compactComparisonSaturation
local notation "I" => Subgroup.comap (Subgroup.subtype (MonoidHom.ker rS))
  (Subgroup.subgroupOf H S)

local instance nativeOrbitJacquetAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance nativeOrbitJacquetAmbientT2 : T2Space (rationalPoints G) :=
  Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
local instance nativeOrbitJacquetKernelMeasurable : MeasurableSpace (MonoidHom.ker rS) := borel _
local instance nativeOrbitJacquetKernelBorel : BorelSpace (MonoidHom.ker rS) := ⟨rfl⟩
local instance nativeOrbitJacquetIntersectionMeasurable : MeasurableSpace I := borel _
local instance nativeOrbitJacquetIntersectionBorel : BorelSpace I := ⟨rfl⟩
local instance nativeOrbitJacquetQuotientMeasurable : MeasurableSpace (LeftQuotient I) := borel _
local instance nativeOrbitJacquetQuotientBorel : BorelSpace (LeftQuotient I) := ⟨rfl⟩

set_option maxHeartbeats 80000 in
/-- The native kernel Jacquet quotient of the original compact orbit piece
is compact induction of its original quotient coefficient and exact Haar scalar.
All analytic inputs are derived from the actual represented radical. -/
def compactComparisonNativeJacquetEquiv (R : D.DynamicRealization)
    (ρ : Representation B H V) (hρ : IsSmooth ρ) :
    Representation.Equiv
      (((compactInduced (R := B) (V := V) H ρ).toCoinvariants (π).ker).comp s)
      (compactInduced (R := B) K
        (D.compactComparisonNativeCoefficient (B := B) (V := V) ρ)) := by
  letI : LocallyCompactSpace (pointImage q) :=
    (isClosed_pointImage q hq.isClosedSubgroup).locallyCompactSpace
  have hπ : Continuous π := continuous_projection_pointImage q lQ rQ hq hlQ hrQ hmulQ
  have hs : Continuous s := continuous_subtype_val.subtype_mk _
  have hN : IsClosed ((π).ker : Set (pointImage q)) :=
    isClosed_singleton.preimage hπ
  let e := Coefficient.splitStagesCoveredCompactEquiv (R := B) (V := V) π s hrs S H
    D.projectionKernel_le_compactComparisonSaturation
    D.isClosed_compactComparisonSaturation hH hN
    (representedProjectionKernel_compactOpenCover (q := q) (lQ := lQ) (rQ := rQ)
      (hq := hq) (hrQ := hrQ) (hmulQ := hmulQ))
    R.stabilizer_le_compactComparisonSaturation hSI ρ hρ hπ hs
  have hχ := D.compactComparisonNativeHaarCharacter_eq_nested (B := B)
  have hc : D.compactComparisonNativeCoefficient (B := B) (V := V) ρ = _ :=
    congrArg (fun χ : K →* Bˣ =>
      Langlands.twist χ (D.compactComparisonNativeSectionCoefficient (B := B) ρ)) hχ
  exact Eq.mpr (congrArg
    (fun τ : Representation B K
        (Jacquet.Coinvariants ρ (Subgroup.comap (Subgroup.subtype H) (π).ker)) =>
      Representation.Equiv
        (((compactInduced (R := B) H ρ).toCoinvariants (π).ker).comp s)
        (compactInduced K τ)) hc) e

/-- Admissibility of the actual intersection quotient and compactness of the
original output quotient imply admissibility of the original native orbit quotient. -/
theorem compactComparisonNativeJacquet_isAdmissible [IsNoetherianRing B]
    [CompactSpace (LeftQuotient K)] (R : D.DynamicRealization)
    (ρ : Representation B H V) (hρ : IsSmooth ρ)
    (hcoeff : IsAdmissible (D.targetStabilizerCoinvariantRepresentation ρ)) :
    IsAdmissible (((compactInduced H ρ).toCoinvariants (π).ker).comp s) :=
  isAdmissible_of_equiv (D.compactComparisonNativeJacquetEquiv R ρ hρ).symm
    (D.compactComparisonNativeCompactInduced_isAdmissible ρ hcoeff)

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
