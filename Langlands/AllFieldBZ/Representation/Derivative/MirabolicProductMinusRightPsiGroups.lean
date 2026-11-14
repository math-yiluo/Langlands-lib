import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusRightPsiZero
import Langlands.AllFieldBZ.Representation.Induction.BinaryPositiveCompact
import Langlands.Representation.Derivative.MirabolicProductMinusRightPsiGroups

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusRightPsiGroups`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductMinusRightPsiGroups` to an arbitrary nonarchimedean local field
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
open Langlands.Derivative.MirabolicProductMinus hiding LeftPhiBoundary LeftPhiCompatibility LeftPsiCompatibility RightPhiBoundary RightPhiShortExact RightPsiCompatibility determinantNorm_rightPsi generalLinearRankCastIso leftPhiExpected leftPhiProduct mirabolicRankCastIso mulEquivHaarChar_conj_levi_inv mulEquivHaarChar_splitKernelConjugation_levi psiMinus_zero_trivial radical_compactOpenBasis radical_compactOpenCover rightBoundaryQuotient rightBoundaryQuotientEquiv rightBoundaryQuotientEquiv_action rightBoundaryQuotientEquiv_natural rightBoundaryTopEquiv rightPhiBoundary rightPhiProduct rightPhiQuotient rightPhiSubobject rightPsiCompatibility_zero rightPsiHaarRatio_apply rightPsiZeroTarget rightPsiZeroTargetEquiv rightPsiZeroTargetEquiv_action rightPsiZeroTargetEquiv_natural twist_rightInducing_levi_zero
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear.Mirabolic hiding leviRadical_haarCharacter radicalCoordinates_isAddHaar radicalHaar_map_leviConj
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic.MixedProduct
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe uF uV

/-! ## The two coordinate blocks of `Fin (m + r)` -/

section Indices
variable {m r : ℕ}

end Indices
/-! ## The parabolic `Q`, its preimage `P`, and the inducing subgroup -/

section Groups
variable {R : Type*} [CommRing R] {m r : ℕ} (hr : 0 < r) (hm : 0 < m)

end Groups
section GroupTopology
variable {R : Type*} [CommRing R] [TopologicalSpace R] [T2Space R] {m r : ℕ}
  (hr : 0 < r) (hm : 0 < m)

end GroupTopology
/-! ## The diagonal blocks of `Q` -/

section Blocks
variable {R : Type*} [CommRing R] {m r : ℕ} (hr : 0 < r) (hm : 0 < m)

end Blocks
/-! ## The inducing elements in the radical -/

section Kernel
variable {R : Type*} [CommRing R] {m r : ℕ}

variable [TopologicalSpace R]

end Kernel
/-! ## The split-stage data of the comparison -/

section Stages
variable {R : Type*} [CommRing R] {m r : ℕ} (hr : 0 < r) (hm : 0 < m)

end Stages
/-! ## The Haar ratio of the two kernels -/

section Haar
open Langlands.Induction
open Langlands.QuotientIntegration
variable {F : LocalFieldPackage.{uF}}

/-- Conjugation by `diag(l, 1)⁻¹` on the radical `ker projection` of `P_(n+1)` scales
Haar measure by `|det l|⁻¹`. -/
theorem mulEquivHaarChar_splitKernelConjugation_levi (T : F.TopologicalData) (n : ℕ)
    (l : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (n + 1)
    letI := T.generalLinearLocallyCompactSpace (n + 1)
    letI := GeneralLinear.Mirabolic.locallyCompactSpace (n := n) (F := F.Carrier)
    ∀ [MeasurableSpace (projection (n := n) (F := F.Carrier)).ker]
      [BorelSpace (projection (n := n) (F := F.Carrier)).ker]
      [LocallyCompactSpace (projection (n := n) (F := F.Carrier)).ker],
      mulEquivHaarChar (splitKernelConjugation (projection (n := n) (F := F.Carrier)) levi l) =
        (T.determinantNorm n l : ℝ≥0)⁻¹ := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := n) (F := F.Carrier)
  intro _ _ _
  have hNr : (projection (n := n) (F := F.Carrier)).ker = radical n F.Carrier := ker_projection
  let : LocallyCompactSpace (radical n F.Carrier) := radical_isClosed.locallyCompactSpace
  let : MeasurableSpace (radical n F.Carrier) := borel _
  have : BorelSpace (radical n F.Carrier) := ⟨rfl⟩
  have hl : (levi l)⁻¹ ∈ Subgroup.normalizer
      (radical n F.Carrier : Set (mirabolic n F.Carrier)) := by
    rw [← hNr]
    simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]
  exact (mulEquivHaarChar_normalizerConj_congr hNr ((levi l)⁻¹)
    (by simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]) hl).trans
    (mulEquivHaarChar_conj_levi_inv T n l hl)

/-- `|det l| = |det A| |det D|` on `Q`. -/
theorem determinantNorm_rightPsi (T : F.TopologicalData) {m r : ℕ} (hr : 0 < r) (hm : 0 < m)
    (l : GeneralLinear (m + r) F.Carrier) (hl : l ∈ rightPsiParabolic (R := F.Carrier) hr hm) :
    T.determinantNorm (m + r) l = T.determinantNorm r (rightPsiFirstBlock hr hm l hl) *
      T.determinantNorm m (rightPsiSecondBlock hr hm l hl) := by
  change T.normalizedAbsUnits (determinant l) =
    T.normalizedAbsUnits (determinant (rightPsiFirstBlock hr hm l hl)) *
      T.normalizedAbsUnits (determinant (rightPsiSecondBlock hr hm l hl))
  rw [determinant_rightPsi hr hm l hl, map_mul]

/-- The Haar character of the two-stage comparison is `|det D|` at `[[A, X], [0, D]]`:
conjugation scales the kernel intersection `≅ V_(r+1)` by `|det A|⁻¹` and the kernel
`≅ V_(m+r+1)` by `|det l|⁻¹ = |det A|⁻¹ |det D|⁻¹`. -/
theorem rightPsiHaarRatio_apply (T : F.TopologicalData) {m r : ℕ} (hr : 0 < r) (hm : 0 < m)
    (l : (rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier))) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (m + r + 1)
    letI := T.generalLinearLocallyCompactSpace (m + r + 1)
    letI := GeneralLinear.Mirabolic.locallyCompactSpace (n := m + r) (F := F.Carrier)
    ∀ [MeasurableSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker]
      [BorelSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker]
      [LocallyCompactSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker]
      [MeasurableSpace ((rightPsiInducing (R := F.Carrier) hr hm).comap
        (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype)]
      [BorelSpace ((rightPsiInducing (R := F.Carrier) hr hm).comap
        (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype)],
      (splitKernelHaarRatio (rightPsiRetraction (R := F.Carrier) hr hm)
          ((levi (n := m + r) (F := F.Carrier)).subgroupComap (rightPsiStages hr hm))
          (rightPsiInducing (R := F.Carrier) hr hm) (rightPsiSection_mem hr hm)
          (isClosed_rightPsiInducing hr hm) l : ℝ≥0) =
        T.determinantNorm m (rightPsiSecondBlock hr hm l.val (rightPsiLevi_mem hr hm l)) := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (m + r + 1)
  let := T.generalLinearLocallyCompactSpace (m + r + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := m + r) (F := F.Carrier)
  intro _ _ _ _ _
  let P := rightPsiStages (R := F.Carrier) hr hm
  let hker := ker_projection_le_rightPsiStages (R := F.Carrier) hr hm
  let rP := rightPsiRetraction (R := F.Carrier) hr hm
  let sP := (levi (n := m + r) (F := F.Carrier)).subgroupComap P
  let HP := rightPsiInducing (R := F.Carrier) hr hm
  let I := HP.comap rP.ker.subtype
  let : LocallyCompactSpace I :=
    (isClosed_splitKernelIntersection rP HP (isClosed_rightPsiInducing hr hm)).locallyCompactSpace
  have hl := rightPsiLevi_mem hr hm l
  set A := rightPsiFirstBlock hr hm l.val hl with hA
  set D := rightPsiSecondBlock hr hm l.val hl with hD
  -- The kernel: `ker rP ≃ ker projection`.
  have hNr : (projection (n := m + r) (F := F.Carrier)).ker = radical (m + r) F.Carrier :=
    ker_projection
  have hNc : IsClosed ((projection (n := m + r) (F := F.Carrier)).ker :
      Set (mirabolic (m + r) F.Carrier)) := by
    rw [hNr]
    exact radical_isClosed
  let : LocallyCompactSpace (projection (n := m + r) (F := F.Carrier)).ker :=
    hNc.locallyCompactSpace
  let : MeasurableSpace (projection (n := m + r) (F := F.Carrier)).ker := borel _
  have : BorelSpace (projection (n := m + r) (F := F.Carrier)).ker := ⟨rfl⟩
  have hN : mulEquivHaarChar (splitKernelConjugation rP sP l) =
      (T.determinantNorm (m + r) l.val : ℝ≥0)⁻¹ := by
    refine (Langlands.Geometric.haarChar_eq_of_conjugacy
      (splitStagesKernelContinuousEquiv projection levi projection_levi P hker)
      (splitKernelConjugation rP sP l)
      (splitKernelConjugation projection levi l.val) (fun g => Subtype.ext ?_)).trans
      (mulEquivHaarChar_splitKernelConjugation_levi T (m + r) l.val)
    change (((splitKernelConjugation rP sP l g : rP.ker) : P) : mirabolic (m + r) F.Carrier) =
      (splitKernelConjugation projection levi l.val
        (splitStagesKernelContinuousEquiv projection levi projection_levi P hker g) :
          mirabolic (m + r) F.Carrier)
    rw [splitKernelConjugation_apply, splitKernelConjugation_apply]
    rfl
  -- The intersection: `I ≃ N ≃ V_(r+1)`.
  let := T.generalLinearTopologicalGroup (r + 1)
  let := T.generalLinearLocallyCompactSpace (r + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := r) (F := F.Carrier)
  let : LocallyCompactSpace (radical r F.Carrier) := radical_isClosed.locallyCompactSpace
  let : MeasurableSpace (radical r F.Carrier) := borel _
  have : BorelSpace (radical r F.Carrier) := ⟨rfl⟩
  have hAn : (levi A)⁻¹ ∈ Subgroup.normalizer
      (radical r F.Carrier : Set (mirabolic r F.Carrier)) := by
    rw [← ker_projection]
    simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]
  have hlH : levi l.val ∈ rightSubgroup m r F.Carrier := levi_mem_rightSubgroup hr hm hl
  have hI : mulEquivHaarChar (subgroupAutomorphism I (splitKernelConjugation rP sP l)
      (splitKernelConjugation_mem rP sP HP (rightPsiSection_mem hr hm) l)) =
      (T.determinantNorm r A : ℝ≥0)⁻¹ := by
    refine (Langlands.Geometric.haarChar_eq_of_conjugacy
      ((splitStagesCoefficientIntersectionContinuousEquiv projection levi projection_levi P
        (rightSubgroup m r F.Carrier) hker (rightSubgroup_le_rightPsiStages hr hm)).trans
        rightPsiKernelContinuousEquiv)
      (subgroupAutomorphism I (splitKernelConjugation rP sP l)
        (splitKernelConjugation_mem rP sP HP (rightPsiSection_mem hr hm) l))
      (HaarModulus.normalizerConj (radical r F.Carrier) ⟨(levi A)⁻¹, hAn⟩)
      (fun i => Subtype.ext ?_)).trans (mulEquivHaarChar_conj_levi_inv T r A hAn)
    have hi : (i.val.val.val : mirabolic (m + r) F.Carrier) ∈ rightSubgroup m r F.Carrier :=
      i.property
    have key : (⟨(levi l.val)⁻¹ * i.val.val.val * levi l.val,
        (rightSubgroup m r F.Carrier).mul_mem
          ((rightSubgroup m r F.Carrier).mul_mem
            ((rightSubgroup m r F.Carrier).inv_mem hlH) hi) hlH⟩ :
          rightSubgroup m r F.Carrier) =
        (⟨levi l.val, hlH⟩ : rightSubgroup m r F.Carrier)⁻¹ * ⟨i.val.val.val, hi⟩ *
          ⟨levi l.val, hlH⟩ := rfl
    change (rightProjection (⟨(levi l.val)⁻¹ * i.val.val.val * levi l.val, _⟩ :
        rightSubgroup m r F.Carrier)).1 =
      (levi A)⁻¹ * (rightProjection (⟨i.val.val.val, hi⟩ : rightSubgroup m r F.Carrier)).1 *
        ((levi A)⁻¹)⁻¹
    rw [key, map_mul, map_mul, map_inv, rightProjection_levi hr hm l.val hl, inv_inv]
    rfl
  -- The ratio.
  simp only [splitKernelHaarRatio_apply]
  rw [hI, hN, determinantNorm_rightPsi T hr hm l.val hl, Units.val_mul, inv_div_inv]
  exact mul_div_cancel_left₀ _ (Units.ne_zero _)

end Haar
end Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
