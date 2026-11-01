import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSection
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHaar
import Langlands.Representation.Induction.SplitStagesCharacterComparison
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Group.GL.CompactOpen

/-! Actual left-orbit character stages comparison with derived p-adic data. -/

noncomputable section

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedOrbit
  Induction Induction.SplitKernelLocalization MeasureTheory MeasureTheory.Measure
  QuotientIntegration HarmonicAnalysis Topology

universe uF uV uW

section KernelTopology

variable {R : Type uF} [CommRing R] [TopologicalSpace R]

/-- Removing the redundant plus-subgroup membership preserves the kernel topology. -/
def plusKernelRadicalContinuousEquiv (n : ℕ) :
    (plusProjection (n := n) (F := R)).ker ≃ₜ* radical (n + 1) R where
  toMulEquiv := plusKernelRadicalEquiv n
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The actual nested stages kernel is an abelian group with its existing operations. -/
abbrev leftPhiStagesKernelCommGroup (k r : ℕ) (i : Fin 2) :
    CommGroup (leftPhiStagesRetraction k r (R := R) i).ker :=
  { (inferInstance : Group (leftPhiStagesRetraction k r (R := R) i).ker) with
    mul_comm := fun a b =>
      ((leftPhiStagesKernelEquiv k r i).trans radicalEquiv).injective (by
        rw [map_mul, map_mul]
        exact mul_comm _ _) }

end KernelTopology

private theorem measureRightOfComm {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [IsMulLeftInvariant μ] (hcomm : ∀ a b : G, a * b = b * a) :
    IsMulRightInvariant μ where
  map_mul_right_eq_self g := by
    rw [show (fun x : G => x * g) = (fun x => g * x) from funext (fun x => hcomm x g)]
    exact map_mul_left_eq_self μ g

section ActualMeasures

variable {R : Type uF} [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R] [T2Space R] (k r : ℕ) (i : Fin 2)
variable [LocallyCompactSpace (GeneralLinear (k + r + 3) R)]

local notation "rP" => leftPhiStagesRetraction k r (R := R) i
local notation "HP" => leftPhiStagesStabilizer k r (R := R) i
local notation "I" => Subgroup.comap (Subgroup.subtype (MonoidHom.ker rP)) HP

local instance stagesKernelLocallyCompact : LocallyCompactSpace (rP).ker :=
  leftPhiHaar_kernel_locallyCompact k r i
local instance stagesKernelMeasurable : MeasurableSpace (rP).ker := borel _
local instance stagesKernelBorel : BorelSpace (rP).ker := ⟨rfl⟩
local instance stagesIntersectionMeasurable : MeasurableSpace I := borel _
local instance stagesIntersectionBorel : BorelSpace I := ⟨rfl⟩
local instance stagesQuotientMeasurable : MeasurableSpace (QuotientIntegration.LeftQuotient I) := borel _
local instance stagesQuotientBorel : BorelSpace (QuotientIntegration.LeftQuotient I) := ⟨rfl⟩
local instance stagesIntersectionLocallyCompact : LocallyCompactSpace I :=
  ((leftPhiHaar_stabilizer_isClosed k r i).preimage continuous_subtype_val).locallyCompactSpace

local instance stagesKernelHaarRight : IsMulRightInvariant (haar : Measure (rP).ker) :=
  measureRightOfComm haar (leftPhiStagesKernelCommGroup k r i).mul_comm
local instance stagesIntersectionHaarRight : IsMulRightInvariant (haar : Measure I) :=
  measureRightOfComm haar (fun a b => Subtype.ext
    ((leftPhiStagesKernelCommGroup k r i).mul_comm a.val b.val))

/-- The actual abelian kernel and intersection admit a compatible quotient measure. -/
theorem leftPhi_stagesCompatibleMeasure_exists :
    ∃ ν : Measure (QuotientIntegration.LeftQuotient I), IsCompatible I haar haar ν := by
  exact compatibleMeasureExists I
    ((leftPhiHaar_stabilizer_isClosed k r i).preimage continuous_subtype_val) haar haar

/-- One compatible measure, independent of the coefficient representation. -/
def leftPhiStagesQuotientMeasure : Measure (QuotientIntegration.LeftQuotient I) :=
  Classical.choose (leftPhi_stagesCompatibleMeasure_exists k r i)

theorem leftPhiStagesQuotientMeasure_compatible :
    IsCompatible I haar haar (leftPhiStagesQuotientMeasure (R := R) k r i) :=
  Classical.choose_spec (leftPhi_stagesCompatibleMeasure_exists k r i)

section Comparison

variable [NonarchimedeanGroup (GeneralLinear (k + r + 3) R)]
variable (ψ : UnitaryAdditiveCharacter R)
variable (hψ : IsOpen ((plusKernelTheta ψ (k + r + 1)).ker :
  Set (plusProjection (n := k + r + 1) (F := R)).ker))
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (σ : Representation ℂ (leftStabilizer k r R i) V) (hσ : IsSmooth σ)

local notation "p" => plusProjection (n := k + r + 1) (F := R)
local notation "s" => plusSuccessor (n := k + r + 1) (F := R)
local notation "P" => leftStages k r R i
local notation "H" => leftStabilizer k r R i
local notation "K" => Subgroup.comap s P

local instance actualMirabolicLocallyCompact : LocallyCompactSpace (mirabolic (k + r + 2) R) :=
  Mirabolic.locallyCompactSpace
local instance actualPlusLocallyCompact : LocallyCompactSpace (plusSubgroup (k + r + 1) R) :=
  plusSubgroup_isClosed.locallyCompactSpace

omit [IsTopologicalRing R] in
private theorem actualPlusBasis :
    ∀ O : Set (plusSubgroup (k + r + 1) R), IsOpen O →
      (1 : plusSubgroup (k + r + 1) R) ∈ O →
        ∃ U : OpenSubgroup (plusSubgroup (k + r + 1) R),
          IsCompact (U : Set (plusSubgroup (k + r + 1) R)) ∧
            (U : Set (plusSubgroup (k + r + 1) R)) ⊆ O := by
  intro O hO h1
  exact compactOpenSubgroupBasis _ O (hO.mem_nhds h1)

private theorem actualKernelBasis :
    ∀ O : Set (rP).ker, IsOpen O → (1 : (rP).ker) ∈ O →
      ∃ U : OpenSubgroup (rP).ker, IsCompact (U : Set (rP).ker) ∧
        (U : Set (rP).ker) ⊆ O := by
  intro O hO h1
  exact compactOpenSubgroupBasis _ O (hO.mem_nhds h1)

/-- The smooth positive character uses the supplied open-kernel proof. -/
def leftPhiComparisonTheta : SmoothCharacter ℂ (p).ker :=
  ⟨plusKernelTheta ψ (k + r + 1), hψ⟩

local notation "θ" => leftPhiComparisonTheta k r ψ hψ
local notation "hθ" => plusKernelTheta_sectionInvariant ψ (k + r + 1)
local notation "hsH" => leftPhiStagesSection_mem k r (R := R) i
local notation "χ" => SplitStagesCharacter.haarCharacter p s plusProjection_plusSuccessor
  P H (leftStages_contains_kernel k r i) (leftStabilizer_isClosed k r R i) hsH
local notation "κ" => SplitStagesCharacter.coefficientAction p s plusProjection_plusSuccessor
  P H (leftStages_contains_kernel k r i) (leftStabilizer_le_stages k r R i)
  (leftStabilizer_isClosed k r R i) hsH θ hθ σ

omit [NonarchimedeanGroup (GeneralLinear (k + r + 3) R)] in
/-- The generic Haar character is exactly one on either actual left section. -/
theorem leftPhiComparisonHaarCharacter_eq_one : χ = 1 := by
  change Jacquet.complexCharacter
    (splitKernelHaarRatio rP (leftPhiStagesSection k r i) HP
      (leftPhiStagesSection_mem k r i) (leftPhiHaar_stabilizer_isClosed k r i)) = 1
  rw [leftPhiStagesHaarRatio_eq_one k r i]
  ext l
  exact map_one _

set_option maxHeartbeats 800000 in
/-- The generic coefficient becomes the full actual section action, by identity on classes. -/
def leftPhiComparisonCoefficientEquiv :
    Representation.Equiv κ (leftPhiStagesAction k r ψ i σ) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' l := by
    change (χ l : ℂ) • leftPhiStagesAction k r ψ i σ l =
      leftPhiStagesAction k r ψ i σ l
    rw [leftPhiComparisonHaarCharacter_eq_one k r i]
    exact one_smul ℂ _

/-- Character-localized compact induction at an actual left orbit, with all
measure choices independent of its coefficient representation. -/
def leftPhiStagesCharacterEquiv :
    (localizedAction p s (plusKernelTheta ψ (k + r + 1)) hθ (compactInduced H σ)).Equiv
      (compactInduced K (leftPhiStagesAction k r ψ i σ)) := by
  let ν := leftPhiStagesQuotientMeasure (R := R) k r i
  have hν := leftPhiStagesQuotientMeasure_compatible (R := R) k r i
  let : ν.Regular := hν.regular
  exact (SplitStagesCharacter.comparisonEquiv p s plusProjection_plusSuccessor
    continuous_plusProjection continuous_plusSuccessor P H
    (leftStages_contains_kernel k r i) (leftStabilizer_le_stages k r R i)
    (leftStages_isClosed k r R i) (leftStabilizer_isClosed k r R i) hsH θ hθ σ hσ
    ν (actualKernelBasis k r i) haar haar hν
    (isClosed_singleton.preimage continuous_plusProjection) (actualPlusBasis k r)).trans
      (compactInducedEquiv K (leftPhiComparisonCoefficientEquiv k r i ψ hψ σ))

variable {τ : Representation ℂ (leftStabilizer k r R i) W} (hτ : IsSmooth τ)

set_option maxHeartbeats 800000 in
/-- The actual stages comparison commutes with all stabilizer intertwiners on
independent coefficient universes and every localized compact function. -/
theorem leftPhiStagesCharacterEquiv_natural (f : σ.IntertwiningMap τ)
    (z : Jacquet.Localization.Coinvariants (compactInduced H σ)
      (p).ker (plusKernelTheta ψ (k + r + 1))) :
    leftPhiStagesCharacterEquiv k r i ψ hψ τ hτ
        (sectionMap p s (plusKernelTheta ψ (k + r + 1)) hθ
          (compactInducedMap H f) z) =
      compactInducedMap K (leftPhiStagesMap k r ψ i f)
        (leftPhiStagesCharacterEquiv k r i ψ hψ σ hσ z) := by
  let ν := leftPhiStagesQuotientMeasure (R := R) k r i
  have hν := leftPhiStagesQuotientMeasure_compatible (R := R) k r i
  let : ν.Regular := hν.regular
  have hn := SplitStagesCharacter.comparisonEquiv_natural p s plusProjection_plusSuccessor
      continuous_plusProjection continuous_plusSuccessor P H
      (leftStages_contains_kernel k r i) (leftStabilizer_le_stages k r R i)
      (leftStages_isClosed k r R i) (leftStabilizer_isClosed k r R i) hsH θ hθ σ hσ
      ν (actualKernelBasis k r i) haar haar hν
      (isClosed_singleton.preimage continuous_plusProjection) (actualPlusBasis k r) hτ f z
  have he := congrArg (compactInducedEquiv K
    (leftPhiComparisonCoefficientEquiv k r i ψ hψ τ)) hn
  exact he

end Comparison

end ActualMeasures

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The positive character on the actual plus kernel is smooth for the supplied topology. -/
def plusKernelSmoothTheta (n : ℕ) :
    letI := T.topology
    SmoothCharacter ℂ (plusProjection (n := n) (F := F.Carrier)).ker := by
  let := T.topology
  exact {
    toMonoidHom := plusKernelTheta ψ n
    isOpen_ker := (T.mirabolicTheta_isOpen_ker ψ n).preimage
      (plusKernelRadicalContinuousEquiv (R := F.Carrier) n).continuous }

/-- Compact open subgroups form a basis in the actual ambient plus subgroup. -/
theorem leftPhi_plus_compactOpenBasis (n : ℕ) :
    letI := T.topology
    ∀ O : Set (plusSubgroup n F.Carrier), IsOpen O → (1 : plusSubgroup n F.Carrier) ∈ O →
      ∃ U : OpenSubgroup (plusSubgroup n F.Carrier),
        IsCompact (U : Set (plusSubgroup n F.Carrier)) ∧
          (U : Set (plusSubgroup n F.Carrier)) ⊆ O := by
  let := T.topology
  let := T.fieldT2
  let := isTopologicalRing_of_topologicalData F T
  let := T.generalLinearLocallyCompactSpace (n + 2)
  let := T.generalLinearNonarchimedean (n + 2)
  let : LocallyCompactSpace (mirabolic (n + 1) F.Carrier) := Mirabolic.locallyCompactSpace
  let : LocallyCompactSpace (plusSubgroup n F.Carrier) := plusSubgroup_isClosed.locallyCompactSpace
  intro O hO h1
  exact compactOpenSubgroupBasis _ O (hO.mem_nhds h1)

/-- The actual stages kernel has a compact open identity-neighborhood basis. -/
theorem leftPhi_stagesKernel_compactOpenBasis (k r : ℕ) (i : Fin 2) :
    letI := T.topology
    ∀ O : Set (leftPhiStagesRetraction k r (R := F.Carrier) i).ker,
      IsOpen O → (1 : (leftPhiStagesRetraction k r (R := F.Carrier) i).ker) ∈ O →
        ∃ U : OpenSubgroup (leftPhiStagesRetraction k r (R := F.Carrier) i).ker,
          IsCompact (U : Set (leftPhiStagesRetraction k r (R := F.Carrier) i).ker) ∧
            (U : Set (leftPhiStagesRetraction k r (R := F.Carrier) i).ker) ⊆ O := by
  let := T.topology
  let := T.fieldT2
  let := isTopologicalRing_of_topologicalData F T
  let := T.generalLinearLocallyCompactSpace (k + r + 3)
  let := T.generalLinearNonarchimedean (k + r + 3)
  let := leftPhiHaar_kernel_locallyCompact k r (R := F.Carrier) i
  intro O hO h1
  exact compactOpenSubgroupBasis _ O (hO.mem_nhds h1)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The actual stages comparison, deriving all topology and Haar data from the
supplied p-adic realization. -/
def padic_leftPhiStagesCharacterEquiv (k r : ℕ) (i : Fin 2)
    (σ : Representation ℂ (leftStabilizer k r F.Carrier i) V)
    (hσ : letI := T.topology; IsSmooth σ) :
    letI := T.topology
    letI := T.fieldT2
    letI := isTopologicalRing_of_topologicalData F T
    (localizedAction
      (plusProjection (n := k + r + 1) (F := F.Carrier))
      (plusSuccessor (n := k + r + 1) (F := F.Carrier))
      (plusKernelTheta ψ (k + r + 1))
      (plusKernelTheta_sectionInvariant ψ (k + r + 1))
      (compactInduced (leftStabilizer k r F.Carrier i) σ)).Equiv
        (compactInduced
          (Subgroup.comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))
            (leftStages k r F.Carrier i))
          (leftPhiStagesAction k r ψ i σ)) := by
  let := T.topology
  let := T.fieldT2
  let := isTopologicalRing_of_topologicalData F T
  let := T.generalLinearLocallyCompactSpace (k + r + 3)
  let := T.generalLinearNonarchimedean (k + r + 3)
  exact leftPhiStagesCharacterEquiv k r i ψ
    (plusKernelSmoothTheta T ψ (k + r + 1)).isOpen_ker σ hσ

set_option maxHeartbeats 800000 in
/-- Supplied-topology comparison is natural on the complete localization, with
independent coefficient carrier universes. -/
theorem padic_leftPhiStagesCharacterEquiv_natural (k r : ℕ) (i : Fin 2)
    {σ : Representation ℂ (leftStabilizer k r F.Carrier i) V}
    {τ : Representation ℂ (leftStabilizer k r F.Carrier i) W}
    (hσ : letI := T.topology; IsSmooth σ)
    (hτ : letI := T.topology; IsSmooth τ)
    (f : σ.IntertwiningMap τ)
    (z : letI := T.topology
      letI := T.fieldT2
      letI := isTopologicalRing_of_topologicalData F T
      Jacquet.Localization.Coinvariants
      (compactInduced (leftStabilizer k r F.Carrier i) σ)
      (plusProjection (n := k + r + 1) (F := F.Carrier)).ker
      (plusKernelTheta ψ (k + r + 1))) :
    letI := T.topology
    letI := T.fieldT2
    letI := isTopologicalRing_of_topologicalData F T
    padic_leftPhiStagesCharacterEquiv T ψ k r i τ hτ
        (sectionMap
          (plusProjection (n := k + r + 1) (F := F.Carrier))
          (plusSuccessor (n := k + r + 1) (F := F.Carrier))
          (plusKernelTheta ψ (k + r + 1))
          (plusKernelTheta_sectionInvariant ψ (k + r + 1))
          (compactInducedMap (leftStabilizer k r F.Carrier i) f) z) =
      compactInducedMap
        (Subgroup.comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))
          (leftStages k r F.Carrier i))
        (leftPhiStagesMap k r ψ i f)
        (padic_leftPhiStagesCharacterEquiv T ψ k r i σ hσ z) := by
  let := T.topology
  let := T.fieldT2
  let := isTopologicalRing_of_topologicalData F T
  let := T.generalLinearLocallyCompactSpace (k + r + 3)
  let := T.generalLinearNonarchimedean (k + r + 3)
  exact leftPhiStagesCharacterEquiv_natural k r i ψ
    (plusKernelSmoothTheta T ψ (k + r + 1)).isOpen_ker σ hσ hτ f z

end Padic

end Langlands.Derivative.MirabolicProductMinus
