import Langlands.Representation.Induction.CoefficientSplitStagesAmbient
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Langlands.Topology.Nonarchimedean.Subgroup

/-! Native split stages with quotient measures derived from the actual kernel cover. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 20000
set_option autoImplicit false

namespace Langlands.Induction.Coefficient

open MeasureTheory MeasureTheory.Measure
open QuotientIntegration HarmonicAnalysis

universe uR uG uL uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
variable [T2Space G] [LocallyCompactSpace G]
variable {L : Type uL} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
variable (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
variable (P H : Subgroup G) (hker : r.ker ≤ P)
variable (hP : IsClosed (P : Set G)) (hH : IsClosed (H : Set G))
variable (hN : IsClosed (r.ker : Set G))

local notation "rP" => splitStagesRetraction r s hrs P hker
local notation "sP" => s.subgroupComap P
local notation "HP" => H.subgroupOf P
local notation "I" => Subgroup.comap
  (Subgroup.subtype (MonoidHom.ker (splitStagesRetraction r s hrs P hker)))
  (H.subgroupOf P)
local notation "hHPc" => hH.preimage (continuous_subtype_val : Continuous P.subtype)

include hN in
omit [NonarchimedeanGroup G] [T2Space G] [LocallyCompactSpace G]
  [TopologicalSpace L] [IsTopologicalGroup L] in
private theorem splitStagesCoveredKernel_closed :
    IsClosed ((rP).ker : Set P) := by
  rw [splitStagesRetraction_ker]
  exact hN.preimage continuous_subtype_val

variable (hcover : ∀ n : r.ker, ∃ U : OpenSubgroup r.ker,
  IsCompact (U : Set r.ker) ∧ n ∈ U)

include hcover in
omit [NonarchimedeanGroup G] [T2Space G] [LocallyCompactSpace G]
  [TopologicalSpace L] [IsTopologicalGroup L] in
/-- The literal ambient kernel cover pulls back through the actual stages
kernel homeomorphism, without a decomposition hypothesis. -/
theorem splitStagesCoveredKernelCover (n : (rP).ker) :
    ∃ U : OpenSubgroup (rP).ker, IsCompact (U : Set (rP).ker) ∧ n ∈ U := by
  let e := splitStagesKernelContinuousEquiv r s hrs P hker
  obtain ⟨U, hU, hn⟩ := hcover (e n)
  refine ⟨U.comap e.toMonoidHom e.continuous, ?_, hn⟩
  exact e.toHomeomorph.isCompact_preimage.mpr hU

include hP hN in
omit [NonarchimedeanGroup G] [T2Space G] [TopologicalSpace L] [IsTopologicalGroup L] in
private theorem splitStagesCoveredKernelLC : LocallyCompactSpace (rP).ker := by
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  exact (splitStagesCoveredKernel_closed r s hrs P hker hN).locallyCompactSpace

include hP hH hN in
omit [NonarchimedeanGroup G] [T2Space G] [TopologicalSpace L] [IsTopologicalGroup L] in
private theorem splitStagesCoveredIntersectionLC : LocallyCompactSpace I := by
  let : LocallyCompactSpace (rP).ker := splitStagesCoveredKernelLC r s hrs P hker hP hN
  exact (isClosed_splitKernelIntersection rP HP hHPc).locallyCompactSpace

variable [MeasurableSpace (splitStagesRetraction r s hrs P hker).ker]
variable [BorelSpace (splitStagesRetraction r s hrs P hker).ker]
variable [MeasurableSpace
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)]
variable [BorelSpace
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)]
variable [MeasurableSpace (LeftQuotient
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))]
variable [BorelSpace (LeftQuotient
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))]

/-- A regular Haar choice on the actual restricted kernel, with local
compactness derived from closedness in the ambient group. -/
def splitStagesCoveredKernelHaar : Measure (rP).ker := by
  letI : LocallyCompactSpace (rP).ker := splitStagesCoveredKernelLC r s hrs P hker hP hN
  exact Measure.haar

/-- A regular Haar choice on the actual closed inducing intersection. -/
def splitStagesCoveredIntersectionHaar : Measure I := by
  letI : LocallyCompactSpace I := splitStagesCoveredIntersectionLC r s hrs P H hker hP hH hN
  exact Measure.haar

local notation "μN" => splitStagesCoveredKernelHaar r s hrs P hker hP hN
local notation "μI" => splitStagesCoveredIntersectionHaar r s hrs P H hker hP hH hN

instance splitStagesCoveredKernelHaar_isHaarMeasure : IsHaarMeasure μN := by
  unfold splitStagesCoveredKernelHaar
  infer_instance

instance splitStagesCoveredKernelHaar_regular : (μN).Regular := by
  unfold splitStagesCoveredKernelHaar
  infer_instance

instance splitStagesCoveredIntersectionHaar_isHaarMeasure : IsHaarMeasure μI := by
  unfold splitStagesCoveredIntersectionHaar
  infer_instance

instance splitStagesCoveredIntersectionHaar_regular : (μI).Regular := by
  unfold splitStagesCoveredIntersectionHaar
  infer_instance

include hcover in
omit [TopologicalSpace L] [IsTopologicalGroup L] in
theorem splitStagesCoveredKernelHaar_rightInvariant : IsMulRightInvariant μN := by
  let : LocallyCompactSpace (rP).ker := splitStagesCoveredKernelLC r s hrs P hker hP hN
  exact (Haar.compactOpenCoverUnimodularity
    (splitStagesCoveredKernelCover r s hrs P hker hcover)).1 μN

include hcover in
omit [MeasurableSpace (rP).ker] [BorelSpace (rP).ker]
  [MeasurableSpace (LeftQuotient I)] [BorelSpace (LeftQuotient I)]
  [TopologicalSpace L] [IsTopologicalGroup L] in
theorem splitStagesCoveredIntersectionHaar_rightInvariant : IsMulRightInvariant μI := by
  let : LocallyCompactSpace (rP).ker := splitStagesCoveredKernelLC r s hrs P hker hP hN
  exact (Haar.compactOpenCoverUnimodularity
    (splitStagesCoveredKernelCover r s hrs P hker hcover)).2 I
      (isClosed_splitKernelIntersection rP HP hHPc) μI

/-- A quotient measure for the actual stages kernel and intersection, selected
from compatible-measure existence for the derived regular two-sided Haar choices. -/
def splitStagesCoveredQuotientMeasure : Measure (LeftQuotient I) := by
  letI : LocallyCompactSpace (rP).ker := splitStagesCoveredKernelLC r s hrs P hker hP hN
  letI : IsMulRightInvariant μN :=
    splitStagesCoveredKernelHaar_rightInvariant r s hrs P hker hP hN hcover
  letI : IsMulRightInvariant μI :=
    splitStagesCoveredIntersectionHaar_rightInvariant r s hrs P H hker hP hH hN hcover
  exact Classical.choose (compatibleMeasureExists I
    (isClosed_splitKernelIntersection rP HP hHPc) μN μI)

local notation "ν" => splitStagesCoveredQuotientMeasure r s hrs P H hker hP hH hN hcover

omit [TopologicalSpace L] [IsTopologicalGroup L] in
/-- The selected measure has the full complex Weil formula for the same actual
kernel and inducing-intersection Haar choices. -/
theorem splitStagesCoveredQuotientMeasure_isCompatible :
    let : IsMulRightInvariant μI :=
      splitStagesCoveredIntersectionHaar_rightInvariant r s hrs P H hker hP hH hN hcover
    IsCompatible I μN μI ν := by
  let : LocallyCompactSpace (rP).ker := splitStagesCoveredKernelLC r s hrs P hker hP hN
  let : IsMulRightInvariant μN :=
    splitStagesCoveredKernelHaar_rightInvariant r s hrs P hker hP hN hcover
  let : IsMulRightInvariant μI :=
    splitStagesCoveredIntersectionHaar_rightInvariant r s hrs P H hker hP hH hN hcover
  exact Classical.choose_spec (compatibleMeasureExists I
    (isClosed_splitKernelIntersection rP HP hHPc) μN μI)

instance splitStagesCoveredQuotientMeasure_regular : (ν).Regular := by
  let : IsMulRightInvariant μI :=
    splitStagesCoveredIntersectionHaar_rightInvariant r s hrs P H hker hP hH hN hcover
  exact (splitStagesCoveredQuotientMeasure_isCompatible r s hrs P H hker hP hH hN hcover).regular

omit [TopologicalSpace L] [IsTopologicalGroup L] in
theorem splitStagesCoveredQuotientMeasure_ne_zero : ν ≠ 0 := by
  let : IsMulRightInvariant μI :=
    splitStagesCoveredIntersectionHaar_rightInvariant r s hrs P H hker hP hH hN hcover
  exact (splitStagesCoveredQuotientMeasure_isCompatible r s hrs P H hker hP hH hN hcover).nonzero

include hP hN in
omit [MeasurableSpace (rP).ker] [BorelSpace (rP).ker]
  [T2Space G] [TopologicalSpace L] [IsTopologicalGroup L] in
private theorem splitStagesCoveredKernelBasis
    (O : Set (rP).ker) (hO : IsOpen O) (h1 : (1 : (rP).ker) ∈ O) :
    ∃ U : OpenSubgroup (rP).ker,
      IsCompact (U : Set (rP).ker) ∧ (U : Set (rP).ker) ⊆ O := by
  let : LocallyCompactSpace (rP).ker := splitStagesCoveredKernelLC r s hrs P hker hP hN
  exact Langlands.compactOpenSubgroupBasis (rP).ker O (hO.mem_nhds h1)

omit [T2Space G] in
private theorem splitStagesCoveredAmbientBasis
    (O : Set G) (hO : IsOpen O) (h1 : (1 : G) ∈ O) :
    ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧ (U : Set G) ⊆ O :=
  Langlands.compactOpenSubgroupBasis G O (hO.mem_nhds h1)

variable {R : Type uR} [CommRing R] [Algebra ℂ R]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable [Module ℂ V] [IsScalarTower ℂ R V]
variable (hHP : H ≤ P) (hsH : ∀ l : P.comap s, s (l : L) ∈ H)
variable (σ : Representation R H V) (hσ : IsSmooth σ)
variable (hr : Continuous r) (hs : Continuous s)

local notation "N" => r.ker.comap H.subtype
local notation "a" => splitStagesInducingSection s P H hsH
local notation "χ" =>
  MonoidHom.comp (Units.map (RingHom.toMonoidHom (algebraMap ℂ R)))
    (Jacquet.complexCharacter (splitKernelHaarRatio rP sP HP (fun l => hsH l) hHPc))
local notation "κA" => twist χ (MonoidHom.comp (Representation.toCoinvariants σ N) a)

/-- Native compact split stages with the original inducing action. Measure and
neighborhood-basis inputs follow from the actual ambient kernel cover. -/
def splitStagesCoveredCompactEquiv :
    letI : LocallyCompactSpace (rP).ker := splitStagesCoveredKernelLC r s hrs P hker hP hN
    Representation.Equiv (((compactInduced H σ).toCoinvariants r.ker).comp s)
      (compactInduced (P.comap s) κA) := by
  letI : LocallyCompactSpace (rP).ker := splitStagesCoveredKernelLC r s hrs P hker hP hN
  letI : IsMulRightInvariant μN :=
    splitStagesCoveredKernelHaar_rightInvariant r s hrs P hker hP hN hcover
  letI : IsMulRightInvariant μI :=
    splitStagesCoveredIntersectionHaar_rightInvariant r s hrs P H hker hP hH hN hcover
  exact splitStagesAmbientCompactEquiv r s hrs P H hker hHP hsH σ hr hs hP hH hσ
    ν (splitStagesCoveredKernelBasis r s hrs P hker hP hN) μN μI
    (splitStagesCoveredQuotientMeasure_isCompatible r s hrs P H hker hP hH hN hcover)
    hN splitStagesCoveredAmbientBasis

/-- Evaluation retains the original function and the original inducing
coinvariant class in the relative integral. -/
@[simp]
theorem splitStagesCoveredCompactEquiv_eval_mk (f : CompactFunctions H σ) (l : L) :
    letI : LocallyCompactSpace (rP).ker := splitStagesCoveredKernelLC r s hrs P hker hP hN
    eval (P.comap s) κA
      (splitStagesCoveredCompactEquiv r s hrs P H hker hP hH hN hcover hHP hsH
        σ hσ hr hs
        (Representation.Coinvariants.mk ((compactInduced H σ).comp r.ker.subtype) f)).val l =
      splitStagesCoefficientEquiv r s hrs P H hker hHP σ
        (splitStagesInnerIntegral r s hrs hr hs P H hker hHP hP hH hsH σ hσ ν
          (splitStagesSlice P H hHP hP hH σ f (s l))) := by
  let : LocallyCompactSpace (rP).ker := splitStagesCoveredKernelLC r s hrs P hker hP hN
  let : IsMulRightInvariant μN :=
    splitStagesCoveredKernelHaar_rightInvariant r s hrs P hker hP hN hcover
  let : IsMulRightInvariant μI :=
    splitStagesCoveredIntersectionHaar_rightInvariant r s hrs P H hker hP hH hN hcover
  exact splitStagesAmbientCompactEquiv_eval_mk r s hrs P H hker hHP hsH σ hr hs hP hH hσ
    ν (splitStagesCoveredKernelBasis r s hrs P hker hP hN) μN μI
    (splitStagesCoveredQuotientMeasure_isCompatible r s hrs P H hker hP hH hN hcover)
    hN splitStagesCoveredAmbientBasis f l

variable {W : Type uW} [AddCommGroup W] [Module R W]
variable [Module ℂ W] [IsScalarTower ℂ R W]
variable {τ : Representation R H W} (hτ : IsSmooth τ) (T : σ.IntertwiningMap τ)

/-- The derived measure choice is independent of the inducing coefficient,
so the full comparison remains natural for every native inducing intertwiner. -/
theorem splitStagesCoveredCompactEquiv_natural
    (z : Representation.Coinvariants ((compactInduced H σ).comp r.ker.subtype)) :
    letI : LocallyCompactSpace (rP).ker := splitStagesCoveredKernelLC r s hrs P hker hP hN
    splitStagesCoveredCompactEquiv r s hrs P H hker hP hH hN hcover hHP hsH
        τ hτ hr hs
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (compactInducedMap H T) r.ker) z) =
      compactInducedMap (P.comap s)
        (splitStagesAmbientCoefficientMap r s hrs P H hker hsH σ hH T)
        (splitStagesCoveredCompactEquiv r s hrs P H hker hP hH hN hcover hHP hsH
          σ hσ hr hs z) := by
  let : LocallyCompactSpace (rP).ker := splitStagesCoveredKernelLC r s hrs P hker hP hN
  let : IsMulRightInvariant μN :=
    splitStagesCoveredKernelHaar_rightInvariant r s hrs P hker hP hN hcover
  let : IsMulRightInvariant μI :=
    splitStagesCoveredIntersectionHaar_rightInvariant r s hrs P H hker hP hH hN hcover
  exact splitStagesAmbientCompactEquiv_natural r s hrs P H hker hHP hsH σ T hr hs hP hH hσ
    ν (splitStagesCoveredKernelBasis r s hrs P hker hP hN) μN μI
    (splitStagesCoveredQuotientMeasure_isCompatible r s hrs P H hker hP hH hN hcover)
    hN splitStagesCoveredAmbientBasis hτ z

end Langlands.Induction.Coefficient
