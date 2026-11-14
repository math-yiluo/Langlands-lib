import Langlands.AllFieldBZ.Group.GL.MirabolicMixedOrbitSectionCoefficients
import Langlands.AllFieldBZ.Group.GL.MirabolicMixedOrbitStages
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicPhiMinusMackey
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusRightPsiGroups
import Langlands.AllFieldBZ.Representation.Induction.SplitStagesCharacterIntegrand
import Langlands.AllFieldBZ.Representation.Mirabolic.LeftMixedProductSuccessor
import Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityGroups

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityGroups`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityGroups` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open MeasureTheory
open MeasureTheory.Measure
open scoped TensorProduct
open scoped NNReal
namespace Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
open Langlands.Derivative.MirabolicProductMinus hiding LeftPhiBoundary LeftPhiCompatibility LeftPsiCompatibility RightPhiBoundary RightPhiShortExact RightPsiCompatibility determinantNorm_rankCast_symm determinantNorm_rightIdentity determinantNorm_rightPsi generalLinearRankCastIso leftPhiExpected leftPhiProduct mirabolicRankCastIso mulEquivHaarChar_conj_levi_inv mulEquivHaarChar_splitKernelConjugation_levi plusKernelThetaSmooth plusKernelThetaSmooth_sectionInvariant psiMinus_zero_trivial radical_compactOpenBasis radical_compactOpenCover rightBoundaryQuotient rightBoundaryQuotientEquiv rightBoundaryQuotientEquiv_action rightBoundaryQuotientEquiv_natural rightBoundaryTopEquiv rightIdentityHaarRatio_apply rightPhiBoundary rightPhiProduct rightPhiQuotient rightPhiSubobject rightPsiCompatibility_zero rightPsiHaarRatio_apply rightPsiZeroTarget rightPsiZeroTargetEquiv rightPsiZeroTargetEquiv_action rightPsiZeroTargetEquiv_natural twist_rightInducing_levi_zero
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear.Mirabolic hiding leviRadical_haarCharacter radicalCoordinates_isAddHaar radicalHaar_map_leviConj
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic.MixedProduct
open Langlands.GeneralLinear.Mirabolic.MixedOrbit hiding isTopologicalRing_of_topologicalData
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe uF uV

/-! ## Stages data at an arbitrary representative -/

section Generic
variable {R : Type*} [CommRing R] {t : ℕ} (H : Subgroup (mirabolic (t + 1) R))
  (w : mirabolic (t + 1) R)

end Generic
/-! ## The kernel character of the plus subgroup -/

section KernelTheta
variable {F : LocalFieldPackage.{uF}}

/-- The restriction of `thetaPlus` to the kernel of `plusProjection`, as a smooth character. -/
def plusKernelThetaSmooth (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (t : ℕ) :
    letI := T.topology
    Induction.SmoothCharacter ℂ (Langlands.Derivative.Mirabolic.plusKernel t F.Carrier) :=
  letI := T.topology
  { toMonoidHom := Langlands.Derivative.Mirabolic.plusKernelTheta ψ t
    isOpen_ker := (T.mirabolicTheta_isOpen_ker ψ t).preimage Langlands.Derivative.Mirabolic.continuous_plusKernelEquiv }

/-- The kernel character is fixed by inverse conjugation by successors. -/
theorem plusKernelThetaSmooth_sectionInvariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (t : ℕ) :
    letI := T.topology
    Induction.SplitKernelLocalization.SectionInvariant (plusProjection (n := t) (F := F.Carrier))
      plusSuccessor (plusKernelThetaSmooth T ψ t).toMonoidHom := by
  let := T.topology
  intro l n
  change Langlands.Derivative.Mirabolic.thetaPlus ψ t ((plusSuccessor l)⁻¹ * (n : plusSubgroup t F.Carrier) *
    plusSuccessor l) = Langlands.Derivative.Mirabolic.thetaPlus ψ t (n : plusSubgroup t F.Carrier)
  rw [map_mul, map_mul, map_inv, Langlands.Derivative.Mirabolic.thetaPlus_plusSuccessor, inv_one, one_mul, mul_one]

end KernelTheta
/-! ## Rank casts and projections -/

section RankCast
variable {R : Type*} [CommRing R]

end RankCast
/-! ## The identity orbit -/

section Identity
variable (k r : ℕ) (R : Type*) [CommRing R]

/- The two subgroups `K` and `rightSection k r R 1` of `P_(k+r+2)` coincide, but not
definitionally; values are compared through `rightIdentityToSection_val`. -/
section Theta
variable [TopologicalSpace R]

end Theta
variable [TopologicalSpace R] [IsTopologicalRing R]

end Identity
/-! ## The split-stage data and its Haar ratio -/

section Stages
variable (k r : ℕ) (R : Type*) [CommRing R]

end Stages
section RankCastNorm
variable {F : LocalFieldPackage.{uF}}

/-- The normalized determinant norm is unchanged by a rank cast. -/
theorem determinantNorm_rankCast_symm (T : F.TopologicalData) {m n : ℕ} (h : m = n)
    (g : mirabolic n F.Carrier) :
    T.determinantNorm (m + 1) ((rankCast h).symm g).val = T.determinantNorm (n + 1) g.val := by
  subst h
  rw [rankCast_rfl_symm_apply]

end RankCastNorm
section Haar
open Langlands.Induction
open Langlands.QuotientIntegration
variable {F : LocalFieldPackage.{uF}}

/-- `ν(l) = ν(A) ν(D)` for `l ∈ K` with lower left blocks `A`, `D`. -/
theorem determinantNorm_rightIdentity (T : F.TopologicalData) (k r : ℕ)
    (l : (rightStages k r F.Carrier 1).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) :
    T.determinantNorm (k + r + 1 + 1) (l : mirabolic (k + r + 1) F.Carrier).val =
      T.determinantNorm (r + 1) (leftProjection (rightIdentityLevi k r F.Carrier l)).1 *
        T.determinantNorm (k + 1) (leftProjection (rightIdentityLevi k r F.Carrier l)).2.val := by
  have h := T.determinantNorm_leftSubgroup (rightIdentityLevi k r F.Carrier l)
  rw [rightIdentityLevi_val, determinantNorm_rankCast_symm] at h
  exact h

/-- The Haar character of the comparison at the identity orbit is `|det D|` at
`l = [[A, B], [0, D]]`: conjugation scales the kernel intersection `≅ V_(r+2)` by
`|det A|⁻¹` and the kernel `≅ V_(k+r+3)` by `|det l|⁻¹ = |det A|⁻¹ |det D|⁻¹`. -/
theorem rightIdentityHaarRatio_apply (T : F.TopologicalData) (k r : ℕ)
    (l : (rightStages k r F.Carrier 1).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    haveI := Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit.isTopologicalRing_of_topologicalData F T
    ∀ [MeasurableSpace (rightIdentityRetraction k r F.Carrier).ker]
      [BorelSpace (rightIdentityRetraction k r F.Carrier).ker]
      [LocallyCompactSpace (rightIdentityRetraction k r F.Carrier).ker]
      [MeasurableSpace ((rightIdentityInducing k r F.Carrier).comap
        (rightIdentityRetraction k r F.Carrier).ker.subtype)]
      [BorelSpace ((rightIdentityInducing k r F.Carrier).comap
        (rightIdentityRetraction k r F.Carrier).ker.subtype)],
      (splitKernelHaarRatio (rightIdentityRetraction k r F.Carrier)
          ((plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap
            (rightStages k r F.Carrier 1))
          (rightIdentityInducing k r F.Carrier) (rightIdentityInducing_section_mem k r F.Carrier)
          ((rightIdStabilizer_isClosed k r F.Carrier).preimage continuous_subtype_val) l : ℝ≥0) =
        T.determinantNorm (k + 1) (leftProjection (rightIdentityLevi k r F.Carrier l)).2.val := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  let := T.generalLinearLocallyCompactSpace (k + r + 1 + 1 + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := k + r + 1 + 1) (F := F.Carrier)
  have := Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit.isTopologicalRing_of_topologicalData F T
  intro _ _ _ _ _
  let P := rightStages k r F.Carrier 1
  let rP := rightIdentityRetraction k r F.Carrier
  let sP := (plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap P
  let HP := rightIdentityInducing k r F.Carrier
  let I := HP.comap rP.ker.subtype
  have hHPc : IsClosed (HP : Set P) :=
    (rightIdStabilizer_isClosed k r F.Carrier).preimage continuous_subtype_val
  let : LocallyCompactSpace I := (isClosed_splitKernelIntersection rP HP hHPc).locallyCompactSpace
  -- The kernel: `ker rP ≃ ker plusProjection ≃ V_(k+r+3)`.
  let : LocallyCompactSpace (radical (k + r + 1 + 1) F.Carrier) :=
    radical_isClosed.locallyCompactSpace
  let : MeasurableSpace (radical (k + r + 1 + 1) F.Carrier) := borel _
  have : BorelSpace (radical (k + r + 1 + 1) F.Carrier) := ⟨rfl⟩
  have hl : (levi (l : mirabolic (k + r + 1) F.Carrier).val)⁻¹ ∈ Subgroup.normalizer
      (radical (k + r + 1 + 1) F.Carrier : Set (mirabolic (k + r + 1 + 1) F.Carrier)) := by
    rw [← ker_projection]
    simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]
  let eN : rP.ker ≃ₜ* radical (k + r + 1 + 1) F.Carrier :=
    (splitStagesKernelContinuousEquiv plusProjection plusSuccessor plusProjection_plusSuccessor P
      (plusKernel_le_stagesSubgroup _ _)).trans (plusKernelContinuousEquiv F.Carrier)
  have hN : mulEquivHaarChar (splitKernelConjugation rP sP l) =
      (T.determinantNorm (k + r + 1 + 1) (l : mirabolic (k + r + 1) F.Carrier).val : ℝ≥0)⁻¹ := by
    refine (Langlands.Geometric.haarChar_eq_of_conjugacy eN (splitKernelConjugation rP sP l)
      (HaarModulus.normalizerConj (radical (k + r + 1 + 1) F.Carrier)
        ⟨(levi (l : mirabolic (k + r + 1) F.Carrier).val)⁻¹, hl⟩) (fun g => Subtype.ext ?_)).trans
      (mulEquivHaarChar_conj_levi_inv T (k + r + 1 + 1) (l : mirabolic (k + r + 1) F.Carrier).val hl)
    change ((((splitKernelConjugation rP sP l g : rP.ker) : P) : plusSubgroup (k + r + 1) F.Carrier) :
        mirabolic (k + r + 1 + 1) F.Carrier) =
      (levi (l : mirabolic (k + r + 1) F.Carrier).val)⁻¹ *
        (((g : rP.ker) : P) : plusSubgroup (k + r + 1) F.Carrier).val *
          ((levi (l : mirabolic (k + r + 1) F.Carrier).val)⁻¹)⁻¹
    rw [splitKernelConjugation_apply, inv_inv]
    rfl
  -- The intersection: `I ≃ S ∩ ker ≃ rightPsiKernel ≃ V_(r+2)`.
  let A := (leftProjection (rightIdentityLevi k r F.Carrier l)).1
  let := T.generalLinearTopologicalGroup (r + 1 + 1)
  let := T.generalLinearLocallyCompactSpace (r + 1 + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := r + 1) (F := F.Carrier)
  let : LocallyCompactSpace (radical (r + 1) F.Carrier) := radical_isClosed.locallyCompactSpace
  let : MeasurableSpace (radical (r + 1) F.Carrier) := borel _
  have : BorelSpace (radical (r + 1) F.Carrier) := ⟨rfl⟩
  have hAn : (levi A)⁻¹ ∈ Subgroup.normalizer
      (radical (r + 1) F.Carrier : Set (mirabolic (r + 1) F.Carrier)) := by
    rw [← ker_projection]
    simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]
  let eI : I ≃ₜ* radical (r + 1) F.Carrier :=
    (splitStagesCoefficientIntersectionContinuousEquiv plusProjection plusSuccessor
      plusProjection_plusSuccessor P (rightIdStabilizer k r F.Carrier)
      (plusKernel_le_stagesSubgroup _ _) (rightIdStabilizer_le_stages k r F.Carrier)).trans
      ((rightIdentityKernelContinuousEquiv k r F.Carrier).trans rightPsiKernelContinuousEquiv)
  have hq : (rightProjection (rightIdentityInclusion k r F.Carrier
      (rightIdentitySectionElement k r F.Carrier l))).1 = levi A := by
    rw [← rightCoefficient_one_apply, rightCoefficient_rightIdentitySectionElement]
  have hI : mulEquivHaarChar (subgroupAutomorphism I (splitKernelConjugation rP sP l)
      (splitKernelConjugation_mem rP sP HP (rightIdentityInducing_section_mem k r F.Carrier) l)) =
      (T.determinantNorm (r + 1) A : ℝ≥0)⁻¹ := by
    refine (Langlands.Geometric.haarChar_eq_of_conjugacy eI
      (subgroupAutomorphism I (splitKernelConjugation rP sP l)
        (splitKernelConjugation_mem rP sP HP (rightIdentityInducing_section_mem k r F.Carrier) l))
      (HaarModulus.normalizerConj (radical (r + 1) F.Carrier) ⟨(levi A)⁻¹, hAn⟩)
      (fun i => Subtype.ext ?_)).trans (mulEquivHaarChar_conj_levi_inv T (r + 1) A hAn)
    let j : rightIdStabilizer k r F.Carrier := ⟨i.val.val.val, i.property⟩
    change (rightProjection (rightIdentityInclusion k r F.Carrier
        ((rightIdentitySectionElement k r F.Carrier l)⁻¹ * j *
          rightIdentitySectionElement k r F.Carrier l))).1 =
      (levi A)⁻¹ * (rightProjection (rightIdentityInclusion k r F.Carrier j)).1 * ((levi A)⁻¹)⁻¹
    simp only [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv, hq, inv_inv]
  -- The ratio.
  simp only [splitKernelHaarRatio_apply]
  rw [hI, hN, determinantNorm_rightIdentity T k r l, Units.val_mul, inv_div_inv]
  exact mul_div_cancel_left₀ _ (Units.ne_zero _)

end Haar
end Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
