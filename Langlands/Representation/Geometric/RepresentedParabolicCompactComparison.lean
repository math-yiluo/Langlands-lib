import Langlands.Representation.Induction.SplitStagesComparison
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups
import Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Topology.CompactOpen.NeighborhoodBasis

/-! # Compact quotient comparison for arbitrary represented parabolics -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Induction MeasureTheory MeasureTheory.Measure QuotientIntegration

private theorem compactOpenCover_of_compactLimit
    {A : Type u} [Group A] [TopologicalSpace A] [NonarchimedeanGroup A]
    {U : Subgroup A} [LocallyCompactSpace U]
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U) :
    ∀ x : U, ∃ K : OpenSubgroup U, IsCompact (K : Set U) ∧ x ∈ K := by
  intro x
  obtain ⟨B, hBc, _⟩ := Langlands.compactOpenSubgroupBasis U Set.univ (by simp)
  obtain ⟨K, hKc, hK⟩ :=
    hU ({x} ∪ (B : Set U)) ((isCompact_singleton).union hBc)
  have hBK : (B : Set U) ⊆ K := fun y hy => hK (Set.mem_union_right _ hy)
  have hKo : IsOpen (K : Set U) :=
    K.isOpen_of_mem_nhds (g := 1)
      (Filter.mem_of_superset (B.isOpen.mem_nhds B.one_mem) hBK)
  exact ⟨⟨K, hKo⟩, hKc, hK (Set.mem_union_left _ (Set.mem_singleton x))⟩

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G Q L U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance compactComparisonPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  (q : Q ⟶ G) (l : L ⟶ Q) (r : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))

local notation "d" =>
  isSemidirectDecomposition_pointImage q l r hq.isClosedSubgroup hr hmul
local notation "π" => IsSemidirectDecomposition.projection d
local notation "s" => Subgroup.inclusion (IsSemidirectDecomposition.levi_le d)
local notation "hrs" => (fun m => IsSemidirectDecomposition.projection_levi d m)

/-- The actual Levi-projection kernel is the original radical point image,
with its inherited topology. -/
def representedProjectionKernelRadicalEquiv :
    (π).ker ≃ₜ* pointImage (r ≫ q) :=
  (subgroupCongrContinuous (by
    ext x
    exact (d).projection_eq_one_iff x)).trans
      (subgroupOfContinuousEquiv (d).unipotent_le)

variable (S H : Subgroup (pointImage q))
  (hker : (IsSemidirectDecomposition.projection
    (isSemidirectDecomposition_pointImage q l r hq.isClosedSubgroup hr hmul)).ker ≤ S)

local notation "rS" => splitStagesRetraction π s hrs S hker
local notation "sS" => MonoidHom.subgroupComap s S
local notation "HS" => H.subgroupOf S
local notation "I" => Subgroup.comap (Subgroup.subtype (MonoidHom.ker rS)) HS

/-- Removing the intermediate subgroup and the parabolic subtype gives the
literal represented radical. -/
def representedNestedKernelRadicalEquiv :
    (rS).ker ≃ₜ* pointImage (r ≫ q) :=
  (splitStagesKernelContinuousEquiv π s hrs S hker).trans
    (representedProjectionKernelRadicalEquiv q l r hq hr hmul)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k]
  [NonarchimedeanGroup (rationalPoints G)] in
theorem representedNestedKernelLocallyCompactSpace :
    LocallyCompactSpace (rS).ker := by
  let : LocallyCompactSpace (pointImage (r ≫ q)) :=
    (isClosed_pointImage_comp q r hq.isClosedSubgroup hr.1.isClosedSubgroup).locallyCompactSpace
  exact (representedNestedKernelRadicalEquiv q l r hq hr hmul S hker).toHomeomorph.isClosedEmbedding.locallyCompactSpace

/-- Every element of the actual nested kernel lies in a compact open subgroup. -/
theorem representedNestedKernel_compactOpenCover :
    ∀ x : (rS).ker, ∃ K : OpenSubgroup (rS).ker,
      IsCompact (K : Set (rS).ker) ∧ x ∈ K := by
  let e := representedNestedKernelRadicalEquiv q l r hq hr hmul S hker
  intro x
  let : LocallyCompactSpace (pointImage (r ≫ q)) :=
    (isClosed_pointImage_comp q r hq.isClosedSubgroup hr.1.isClosedSubgroup).locallyCompactSpace
  obtain ⟨K, hK, hx⟩ := compactOpenCover_of_compactLimit
    (isLimitOfCompactSubgroups_pointImage_radical q r hq.isClosedSubgroup hr.1) (e x)
  exact ⟨OpenSubgroup.comap e.toMonoidHom e.continuous K,
    e.toHomeomorph.isClosedEmbedding.isCompact_preimage hK, hx⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The original nested kernel has the compact open basis used by relative integration. -/
theorem representedNestedKernel_compactOpenBasis :
    ∀ O : Set (rS).ker, IsOpen O → (1 : (rS).ker) ∈ O →
      ∃ K : OpenSubgroup (rS).ker,
        IsCompact (K : Set (rS).ker) ∧ (K : Set (rS).ker) ⊆ O := by
  let : LocallyCompactSpace (rS).ker :=
    representedNestedKernelLocallyCompactSpace q l r hq hr hmul S hker
  intro O hO h1
  exact Langlands.compactOpenSubgroupBasis _ O (hO.mem_nhds h1)

include hq in
omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The actual represented parabolic has a compact open identity-neighborhood basis. -/
theorem representedParabolic_compactOpenBasis :
    ∀ O : Set (pointImage q), IsOpen O → (1 : pointImage q) ∈ O →
      ∃ K : OpenSubgroup (pointImage q),
        IsCompact (K : Set (pointImage q)) ∧ (K : Set (pointImage q)) ⊆ O := by
  let : LocallyCompactSpace (pointImage q) :=
    (isClosed_pointImage q hq.isClosedSubgroup).locallyCompactSpace
  intro O hO h1
  exact Langlands.compactOpenSubgroupBasis _ O (hO.mem_nhds h1)

variable (hH : IsClosed (H : Set (pointImage q)))

include hH in
/-- Two-sided Haar measures and a compatible locally finite quotient measure
exist for the actual nested kernel and its closed stabilizer intersection. -/
theorem representedNested_measureExists :
    letI : MeasurableSpace (rS).ker := borel _
    letI : BorelSpace (rS).ker := ⟨rfl⟩
    letI : MeasurableSpace I := borel _
    letI : BorelSpace I := ⟨rfl⟩
    letI : MeasurableSpace (QuotientIntegration.LeftQuotient I) := borel _
    letI : BorelSpace (QuotientIntegration.LeftQuotient I) := ⟨rfl⟩
    ∃ (μN : Measure (rS).ker) (μI : Measure I),
      IsHaarMeasure μN ∧ μN.Regular ∧ IsMulRightInvariant μN ∧
      IsHaarMeasure μI ∧ μI.Regular ∧
      ∃ hI : IsMulRightInvariant μI,
        letI := hI
        ∃ ν : Measure (QuotientIntegration.LeftQuotient I), IsFiniteMeasureOnCompacts ν ∧
          IsCompatible I μN μI ν := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  let : LocallyCompactSpace (rS).ker :=
    representedNestedKernelLocallyCompactSpace q l r hq hr hmul S hker
  let : MeasurableSpace (rS).ker := borel _
  let : BorelSpace (rS).ker := ⟨rfl⟩
  let : MeasurableSpace I := borel _
  let : BorelSpace I := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient I) := borel _
  let : BorelSpace (QuotientIntegration.LeftQuotient I) := ⟨rfl⟩
  have hI : IsClosed (I : Set (rS).ker) :=
    (hH.preimage continuous_subtype_val).preimage continuous_subtype_val
  let : LocallyCompactSpace I := hI.locallyCompactSpace
  have hu := Haar.compactOpenCoverUnimodularity
    (representedNestedKernel_compactOpenCover q l r hq hr hmul S hker)
  let μN : Measure (rS).ker := haar
  let μI : Measure I := haar
  let : IsMulRightInvariant μN := hu.1 μN
  let : IsMulRightInvariant μI := hu.2 I hI μI
  obtain ⟨ν, hν⟩ := compatibleMeasureExists I hI μN μI
  let : ν.Regular := hν.regular
  exact ⟨μN, μI, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ν, inferInstance, hν⟩


variable (hHP : H ≤ S) (hS : IsClosed (S : Set (pointImage q)))
  (hsH : ∀ m : S.comap (Subgroup.inclusion
    (isSemidirectDecomposition_pointImage q l r hq.isClosedSubgroup hr hmul).levi_le),
    Subgroup.inclusion
      (isSemidirectDecomposition_pointImage q l r hq.isClosedSubgroup hr hmul).levi_le
      (m : pointImage (l ≫ q)) ∈ H)

local notation "hSI" => (fun m => hsH m)
local notation "hHSc" => hH.preimage (continuous_subtype_val : Continuous S.subtype)
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP)

/-- Natural compact-comparison families with the original kernel quotient and
its literal Haar-ratio-corrected coefficient action. -/
def representedCompactComparisonFamily : Type (max u (v + 1)) :=
  letI : LocallyCompactSpace (rS).ker :=
    representedNestedKernelLocallyCompactSpace q l r hq hr hmul S hker
  letI : MeasurableSpace (rS).ker := borel _
  letI : BorelSpace (rS).ker := ⟨rfl⟩
  letI : MeasurableSpace I := borel _
  letI : BorelSpace I := ⟨rfl⟩
  { E : ∀ A : SmoothRep.{0,u,v} ℂ H,
      Representation.Equiv
        (((compactInduced H A.representation).toCoinvariants (π).ker).comp s)
        (compactInduced (S.comap s)
          (twist (Jacquet.complexCharacter (splitKernelHaarRatio rS sS HS hSI hHSc))
            (splitKernelCoefficientAction rS sS HS hSI (A.representation.comp φ)))) //
    ∀ (A A' : SmoothRep.{0,u,v} ℂ H) (f : A ⟶ A') z,
      E A' (Representation.Coinvariants.map _ _
        (Jacquet.restrictMap (compactInducedMap H (SmoothRep.hom f)) (π).ker) z) =
      compactInducedMap (S.comap s)
        (splitStagesCoefficientMap π s hrs S H hker hHP hH hsH A.representation
          (SmoothRep.hom f)) (E A z) }

include hl hS in
/-- One common choice of compatible quotient measures yields a natural family
for all smooth coefficient objects and every coefficient morphism. -/
theorem representedCompactComparison_nonempty :
    Nonempty (representedCompactComparisonFamily.{u,v} q l r hq hr hmul S H hker hH
      hHP hsH) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  let : LocallyCompactSpace (pointImage q) :=
    (isClosed_pointImage q hq.isClosedSubgroup).locallyCompactSpace
  let : LocallyCompactSpace (rS).ker :=
    representedNestedKernelLocallyCompactSpace q l r hq hr hmul S hker
  let : MeasurableSpace (rS).ker := borel _
  let : BorelSpace (rS).ker := ⟨rfl⟩
  let : MeasurableSpace I := borel _
  let : BorelSpace I := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient I) := borel _
  let : BorelSpace (QuotientIntegration.LeftQuotient I) := ⟨rfl⟩
  have hm := representedNested_measureExists q l r hq hr hmul S H hker hH
  obtain ⟨μN, μI, hμN, hμNr, hμNri, hμI, hμIr, hμIri, ν, hν, hc⟩ := hm
  let := hμN
  let := hμNr
  let := hμNri
  let := hμI
  let := hμIr
  let := hμIri
  let := hν
  have hπ : Continuous π := continuous_projection_pointImage q l r hq hl hr hmul
  have hs : Continuous s := continuous_subtype_val.subtype_mk _
  have hN : IsClosed ((π).ker : Set (pointImage q)) :=
    isClosed_singleton.preimage hπ
  let E := fun A : SmoothRep.{0,u,v} ℂ H =>
    splitStagesCompactEquiv π s hrs hπ hs S H hker hHP hS hH hsH
      A.representation A.isSmooth ν
      (representedNestedKernel_compactOpenBasis q l r hq hr hmul S hker)
      μN μI hc hN (representedParabolic_compactOpenBasis q hq)
  refine ⟨E, ?_⟩
  intro A A' f z
  exact splitStagesCompactEquiv_natural π s hrs hπ hs S H hker hHP hS hH hsH
    A.representation A.isSmooth ν
    (representedNestedKernel_compactOpenBasis q l r hq hr hmul S hker)
    μN μI hc A'.isSmooth (SmoothRep.hom f) hN
    (representedParabolic_compactOpenBasis q hq) z

/-- A chosen natural family for the actual represented parabolic. All analytic
inputs are derived from its original radical, rather than supplied as premises. -/
def representedCompactComparison :
    representedCompactComparisonFamily.{u,v} q l r hq hr hmul S H hker hH hHP hsH :=
  Classical.choice
    (representedCompactComparison_nonempty q l r hq hl hr hmul S H hker hH hHP hS hsH)

end Langlands.Aubert.General.RepresentedParabolic
