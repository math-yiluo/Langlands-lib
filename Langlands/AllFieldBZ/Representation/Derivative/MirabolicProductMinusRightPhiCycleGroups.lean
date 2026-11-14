import Langlands.AllFieldBZ.Group.GL.MirabolicMixedOrbitRadicals
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusRightPhiIdentityGroups
import Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleGroups

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleGroups`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleGroups` to an arbitrary nonarchimedean local field
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
open Langlands.Derivative.MirabolicProductMinus hiding LeftPhiBoundary LeftPhiCompatibility LeftPsiCompatibility RightPhiBoundary RightPhiShortExact RightPsiCompatibility determinantNorm_rankCast_symm determinantNorm_rightCycle determinantNorm_rightIdentity determinantNorm_rightPsi determinantNorm_rightSubgroup generalLinearRankCastIso leftPhiExpected leftPhiProduct mirabolicRankCastIso mulEquivHaarChar_conj_levi_inv mulEquivHaarChar_splitKernelConjugation_levi plusKernelThetaSmooth plusKernelThetaSmooth_sectionInvariant psiMinus_zero_trivial radical_compactOpenBasis radical_compactOpenCover rightBoundaryQuotient rightBoundaryQuotientEquiv rightBoundaryQuotientEquiv_action rightBoundaryQuotientEquiv_natural rightBoundaryTopEquiv rightCycleHaarRatio_apply rightIdentityHaarRatio_apply rightPhiBoundary rightPhiProduct rightPhiQuotient rightPhiSubobject rightPsiCompatibility_zero rightPsiHaarRatio_apply rightPsiZeroTarget rightPsiZeroTargetEquiv rightPsiZeroTargetEquiv_action rightPsiZeroTargetEquiv_natural twist_rightInducing_levi_zero
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

/-! ## Determinants of the right mixed subgroup -/

section Determinant
variable {R : Type*} [CommRing R] {k n : ℕ}

variable {F : LocalFieldPackage.{uF}}

/-- `ν(h) = ν(p) ν(a)` for `h ∈ rightSubgroup` with diagonal blocks `(p, a)`. -/
theorem determinantNorm_rightSubgroup (T : F.TopologicalData) (g : rightSubgroup k n F.Carrier) :
    T.determinantNorm (k + n + 1) (g : mirabolic (k + n) F.Carrier).val =
      T.determinantNorm (n + 1) (rightProjection g).1.val *
        T.determinantNorm k (rightProjection g).2 := by
  change T.normalizedAbsUnits (determinant _) =
    T.normalizedAbsUnits (determinant _) * T.normalizedAbsUnits (determinant _)
  rw [← map_mul]
  congr 1
  exact Units.ext (det_rightSubgroup g)

end Determinant
/-! ## The cyclic orbit -/

section Cycle
variable (k r : ℕ) (R : Type*) [CommRing R]

private theorem _root_.Langlands.Derivative.MirabolicProductMinus.projection_conj_eq_one {n : ℕ} (w x : mirabolic n R) (hx : projection x = 1) :
    projection (w⁻¹ * x * w) = 1 := by
  rw [map_mul, map_mul, map_inv, hx, mul_one, inv_mul_cancel]

section Theta
variable [TopologicalSpace R]

end Theta
variable [TopologicalSpace R] [IsTopologicalRing R]

end Cycle
/-! ## The split-stage data and its Haar ratio -/

section Stages
variable (k r : ℕ) (R : Type*) [CommRing R]

end Stages
section Haar
open Langlands.Induction
open Langlands.QuotientIntegration
variable {F : LocalFieldPackage.{uF}}

/-- `ν(l) = ν(p) ν(a)` for `l ∈ K` with lower right blocks `p`, `a`. -/
theorem determinantNorm_rightCycle (T : F.TopologicalData) (k r : ℕ)
    (l : (rightStages k r F.Carrier 0).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) :
    T.determinantNorm (k + r + 1 + 1) (l : mirabolic (k + r + 1) F.Carrier).val =
      T.determinantNorm (r + 1) (rightProjection (rightCycleLevi k r F.Carrier l)).1.val *
        T.determinantNorm (k + 1) (rightProjection (rightCycleLevi k r F.Carrier l)).2 := by
  have h := determinantNorm_rightSubgroup T (rightCycleLevi k r F.Carrier l)
  rw [rightCycleLevi_val, determinantNorm_rankCast_symm] at h
  exact h

/-- The Haar character of the comparison at the cyclic orbit is `|det a|` at
`l = [[p, X], [0, a]]`: conjugation scales the kernel intersection `≅ V_(r+2)` by
`|det p|⁻¹` and the kernel `≅ V_(k+r+3)` by `|det l|⁻¹ = |det p|⁻¹ |det a|⁻¹`. -/
theorem rightCycleHaarRatio_apply (T : F.TopologicalData) (k r : ℕ)
    (l : (rightStages k r F.Carrier 0).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    haveI := Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit.isTopologicalRing_of_topologicalData F T
    ∀ [MeasurableSpace (rightCycleRetraction k r F.Carrier).ker]
      [BorelSpace (rightCycleRetraction k r F.Carrier).ker]
      [LocallyCompactSpace (rightCycleRetraction k r F.Carrier).ker]
      [MeasurableSpace ((rightCycleInducing k r F.Carrier).comap
        (rightCycleRetraction k r F.Carrier).ker.subtype)]
      [BorelSpace ((rightCycleInducing k r F.Carrier).comap
        (rightCycleRetraction k r F.Carrier).ker.subtype)],
      (splitKernelHaarRatio (rightCycleRetraction k r F.Carrier)
          ((plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap
            (rightStages k r F.Carrier 0))
          (rightCycleInducing k r F.Carrier) (rightCycleInducing_section_mem k r F.Carrier)
          ((rightCycStabilizer_isClosed k r F.Carrier).preimage continuous_subtype_val) l : ℝ≥0) =
        T.determinantNorm (k + 1) (rightProjection (rightCycleLevi k r F.Carrier l)).2 := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  let := T.generalLinearLocallyCompactSpace (k + r + 1 + 1 + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := k + r + 1 + 1) (F := F.Carrier)
  have := Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit.isTopologicalRing_of_topologicalData F T
  intro _ _ _ _ _
  let P := rightStages k r F.Carrier 0
  let rP := rightCycleRetraction k r F.Carrier
  let sP := (plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap P
  let HP := rightCycleInducing k r F.Carrier
  let I := HP.comap rP.ker.subtype
  have hHPc : IsClosed (HP : Set P) :=
    (rightCycStabilizer_isClosed k r F.Carrier).preimage continuous_subtype_val
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
  let A := (rightProjection (rightCycleLevi k r F.Carrier l)).1.val
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
      plusProjection_plusSuccessor P (rightCycStabilizer k r F.Carrier)
      (plusKernel_le_stagesSubgroup _ _) (rightCycStabilizer_le_stages k r F.Carrier)).trans
      ((rightCycleKernelContinuousEquiv k r F.Carrier).trans rightPsiKernelContinuousEquiv)
  have hq : (rightProjection (rightCycleInclusion k r F.Carrier
      (rightCycleSectionElement k r F.Carrier l))).1 = levi A := by
    rw [← rightCoefficient_zero_apply, rightCoefficient_rightCycleSectionElement]
    rfl
  have hI : mulEquivHaarChar (subgroupAutomorphism I (splitKernelConjugation rP sP l)
      (splitKernelConjugation_mem rP sP HP (rightCycleInducing_section_mem k r F.Carrier) l)) =
      (T.determinantNorm (r + 1) A : ℝ≥0)⁻¹ := by
    refine (Langlands.Geometric.haarChar_eq_of_conjugacy eI
      (subgroupAutomorphism I (splitKernelConjugation rP sP l)
        (splitKernelConjugation_mem rP sP HP (rightCycleInducing_section_mem k r F.Carrier) l))
      (HaarModulus.normalizerConj (radical (r + 1) F.Carrier) ⟨(levi A)⁻¹, hAn⟩)
      (fun i => Subtype.ext ?_)).trans (mulEquivHaarChar_conj_levi_inv T (r + 1) A hAn)
    let j : rightCycStabilizer k r F.Carrier := ⟨i.val.val.val, i.property⟩
    change (rightProjection (rightCycleInclusion k r F.Carrier
        ((rightCycleSectionElement k r F.Carrier l)⁻¹ * j *
          rightCycleSectionElement k r F.Carrier l))).1 =
      (levi A)⁻¹ * (rightProjection (rightCycleInclusion k r F.Carrier j)).1 * ((levi A)⁻¹)⁻¹
    simp only [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv, hq, inv_inv]
  -- The ratio.
  simp only [splitKernelHaarRatio_apply]
  rw [hI, hN, determinantNorm_rightCycle T k r l, Units.val_mul, inv_div_inv]
  exact mul_div_cancel_left₀ _ (Units.ne_zero _)

end Haar
end Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
