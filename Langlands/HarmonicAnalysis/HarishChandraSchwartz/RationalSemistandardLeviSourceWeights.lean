import Langlands.GroupScheme.Rational.SemistandardProperLeviRank
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalSemistandardComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviXiReversal
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardConstantTermEstimate
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTermEstimateProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSpecialPacketCompact
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFourierOrbitSmoothness

/-! # The constant-term weights of the actual outer Levi model -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.Aubert.General Langlands.GroupScheme Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  {p : SemistandardSpectralIndex i} (m : LeviModel p)

local instance sourceWeightsModelAffine (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    IsAffineHom m.scheme.X.hom := m.reductive.isAffineHom
local instance sourceWeightsModelFiniteType (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    LocallyOfFiniteType m.scheme.X.hom := by
  let := m.reductive.smooth
  infer_instance

set_option hygiene false in
local notation "iM" => semistandardLeviSplitTorus p m.represents

variable {νM : cocharacterLattice S} {KM : OpenSubgroup (rationalPoints m.scheme)}
  (hKM : IsCompact (KM : Set (rationalPoints m.scheme)))
  (hPMK : IsIwasawaPair (standardParabolicPoints iM νM ∅) KM.toSubgroup)

/-- The spherical function of the actual Levi scheme, read as a weight
on the literal Levi subgroup along its point homeomorphism. -/
def LeviModel.literalXi : levi p → ℝ :=
  rationalXi hKM hPMK ∘ m.pointHomeomorph.symm

omit [LocallyOfFiniteType G.X.hom] in
@[simp]
theorem LeviModel.literalXi_pointHomeomorph (x : rationalPoints m.scheme) :
    m.literalXi hKM hPMK (m.pointHomeomorph x) = rationalXi hKM hPMK x := by
  simp only [LeviModel.literalXi, Function.comp_apply, ContinuousMulEquiv.symm_apply_apply]

variable {ν : cocharacterLattice S} {K : OpenSubgroup (rationalPoints G)}
  (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (μU : Measure (radical p)) [μU.IsHaarMeasure]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
/-- The normalized constant-term estimate has target the spherical weight
of the specified actual outer Levi at the inherited compact trace. -/
theorem LeviModel.constantTermEstimate_literalXi (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hνM : IsGenericCocharacter iM νM) (hρ : IsClosedSubgroup ρ)
    (htrace : ∀ x : rationalPoints m.scheme, x ∈ KM ↔ rationalPoints.map m.inclusion x ∈ K) :
    ConstantTermEstimate μU (semistandardUnipotentModulus p)
      (rationalXi hK hPK) (rationalHeight (F := F) ρ) (m.literalXi hKM hPMK)
      (fun x => rationalHeight (F := F) ρ (x : rationalPoints G)) ∧
    TranslationWeights (m.literalXi hKM hPMK)
      (fun x => rationalHeight (F := F) ρ (x : rationalPoints G)) := by
  obtain ⟨ξ, hξ, J, hJ, hp⟩ := exists_standard_presentation hG hi p
  subst p
  let p := SemistandardSpectralIndex.ofStandard hG hi ξ hξ J hJ
  let L : Subgroup (rationalPoints G) := standardLeviPoints i ξ J
  let hQ := (standardParabolicPoints i ξ ∅).subgroupOf L
  let iL := semistandardLeviSplitTorus p m.represents
  have hiL : IsMaximalSplitTorus iL :=
    isMaximalSplitTorus_semistandardLeviSplitTorus p m.represents m.closed hi
  have hξL : IsGenericCocharacter iL ξ := fun α hα =>
    hξ α (relativeRoots_subset_of_factor m.represents iL
      (semistandardLeviSplitTorus_comp p m.represents) hα)
  have hPKξ := IsIwasawaPair.rationalChangeMinimal hG hi hν hξ hPK
  let hPLξ := IsIwasawaPair.rationalChangeMinimal m.reductive hiL hνM hξL hPMK
  let e : rationalPoints m.scheme ≃ₜ* L := m.pointHomeomorph
  have hP (x : rationalPoints m.scheme) : x ∈ standardParabolicPoints iL ξ ∅ ↔ e x ∈ hQ := by
    have hPar : standardParabolic iL ξ ∅ = (standardParabolic i ξ ∅).comap m.inclusion := by
      rw [standardParabolic_empty_eq_dynamic_of_generic iL ξ m.reductive hiL hξL,
        standardParabolic_empty_eq_dynamic_of_generic i ξ hG hi hξ]
      simpa only [Category.assoc, iL, semistandardLeviSplitTorus_comp] using
        Dynamic.parabolic_eq_comap_of_isClosedSubgroup (CommGroupScheme.groupHom ξ ≫ iL)
          m.inclusion m.closed
    change x ∈ (standardParabolic iL ξ ∅).carrier (Over.mk (𝟙 _)) ↔
      (e x : rationalPoints G) ∈ standardParabolicPoints i ξ ∅
    rw [hPar]
    exact Iff.rfl
  have hKtrace (x : rationalPoints m.scheme) : x ∈ KM.toSubgroup ↔ e x ∈ K.toSubgroup.subgroupOf L :=
    htrace x
  let hMK := hPLξ.transport e.toMulEquiv hP hKtrace
  let eP := subgroupContinuousMulEquiv e hP
  let : LocallyCompactSpace (standardParabolicPoints iL ξ ∅) :=
    (isClosed_standardParabolicPoints_empty m.reductive hiL hξL).locallyCompactSpace
  let : LocallyCompactSpace L := (isClosed_standardLeviPoints i ξ J).locallyCompactSpace
  let : LocallyCompactSpace hQ :=
    ((isClosed_standardParabolicPoints_empty hG hi hξ).preimage
      (continuous_subtype_val : Continuous (Subtype.val : L → rationalPoints G))).locallyCompactSpace
  let : CompactSpace KM.toSubgroup := isCompact_iff_compactSpace.mp hKM
  let := compactSpace_subgroupOf_standardLevi (i := i) (ν := ξ) (J := J) hK
  have hmod (q : standardParabolicPoints iL ξ ∅) :
      standardLeviMinimalModulusOf i ξ J ⟨e q, (hP q).mp q.property⟩ =
        rationalMinimalModulus iL ξ q := by
    apply Units.ext
    rw [standardLeviMinimalModulusOf_eq_modularCharacter hG hi hξ hJ,
      rationalMinimalModulus_eq_modularCharacter m.reductive hiL hξL]
    exact modularCharacter_continuousMulEquiv eP q
  have hXiPoint (x : rationalPoints m.scheme) :
      rationalXi hKM hPLξ x = rationalLeviXi hK hMK (e x) := by
    unfold rationalXi rationalLeviXi
    exact (xi_map (hPK := hPLξ) (hPK' := hMK) e
      (fun q hq => standardLeviMinimalModulusOf_eq_one K.isOpen hK hG hi hξ hJ q hq)
      (fun q hq => (hP q).mp hq) hKtrace hmod x).symm
  have he : m.literalXi hKM hPMK = rationalLeviXi hK hMK := by
    funext x
    obtain ⟨z, rfl⟩ := e.surjective x
    change m.literalXi hKM hPMK (m.pointHomeomorph z) = rationalLeviXi hK hMK (e z)
    rw [m.literalXi_pointHomeomorph]
    exact (rationalXi_changeMinimal m.reductive hiL hνM hξL KM.isOpen hKM hPMK hPLξ z).symm.trans
      (hXiPoint z)
  obtain ⟨K0, hK0, _, _, hbasis, hcover, hLeviCover⟩ := hasSpecialPacketCompact hi ξ hG hξ
  let νU : Measure (standardUnipotentPoints i ξ J) := μU
  let : νU.IsHaarMeasure := inferInstanceAs μU.IsHaarMeasure
  have hE := rationalConstantTermEstimate.constantTermEstimate hG hi hξ hJ K0.isOpen hK0
    hbasis hcover (hLeviCover J hJ) K.isOpen hK hPKξ hMK hρ νU
  rw [funext (rationalXi_changeMinimal hG hi hν hξ K.isOpen hK hPK hPKξ)] at hE
  rw [he]
  exact ⟨hE, rationalLeviTranslationWeights hG hi hξ hJ K.isOpen hK hMK ρ⟩

end Langlands.HarishChandraSchwartz.RationalSemistandard
