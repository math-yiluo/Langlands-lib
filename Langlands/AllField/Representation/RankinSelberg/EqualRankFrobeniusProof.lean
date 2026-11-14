import Langlands.Representation.RankinSelberg.EqualRankFrobeniusProof
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankFrobeniusStatement
import Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof
/-!
# Proof of the equal-rank Frobenius equivalence

The equivalence is constructed directly on the nonzero-row orbit, using an
additive Haar measure on row space and its determinant scaling. See the paired
Markdown for the route and its correspondence with JPSS (2.10.5)--(2.10.6).
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFrobeniusStatement EqualRankTrilinearUniquenessStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement equalRankFrobenius lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF uV uW

namespace EqualRankFrobenius
open Langlands.RankinSelberg.EqualRankFrobenius
open Langlands.AllField.RankinSelberg.EqualRankFrobenius
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFrobeniusStatement EqualRankTrilinearUniquenessStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement equalRankFrobenius lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear
open Langlands.RankinSelberg.TrilinearReduction hiding equalRankTrilinearUniqueness_of_source source_uniqueness_of_mirabolic_bound
open Langlands.AllField.RankinSelberg.TrilinearReduction
open scoped Matrix NNReal

section Geometry



end Geometry

section Indicator


end Indicator

section Mass


end Mass

section Decomposition


end Decomposition

section Determinant


end Determinant

section Backward



end Backward

section Value


end Value

section Choice



end Choice

section BackwardMap




end BackwardMap

section Forward




end Forward

section ForwardMap


end ForwardMap

end EqualRankFrobenius

open _root_.MeasureTheory
open Langlands.RankinSelberg.EqualRankFrobenius
open Langlands.AllField.RankinSelberg.EqualRankFrobenius
open scoped Matrix NNReal

/-- The published equal-rank Frobenius equivalence: invariant trilinear forms on row test
functions vanishing at zero, with determinant weight `-s`, are complex-linearly equivalent to
mirabolic covariant bilinear forms with weight `1 - s`. -/
theorem equalRankFrobenius (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) : EqualRankFrobeniusStatement.{uF, uV, uW} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F := T.fieldT2
  have : SecondCountableTopology F := T.secondCountableTopology
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  intro V _ _ W _ _ ρ σ hρ hσ s
  let μ : Measure (Fin (n + 1) → F) := Measure.addHaar
  have hχ (a : F) (ha : a ≠ 0) :
      (Measure.addHaar : Measure F).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • Measure.addHaar :=
    Langlands.AllField.HarmonicAnalysis.padicScalarHaarScaling F T Measure.addHaar (Units.mk0 a ha)
  have hscale : ∀ k : Langlands.GeneralLinear (n + 1) F,
      μ.map (fun x => x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) =
        (T.normalizedAbsHom (Matrix.det (k : Matrix (Fin (n + 1)) (Fin (n + 1)) F)))⁻¹ •
          μ := by
    intro k
    have hM : Matrix.det (k : Matrix (Fin (n + 1)) (Fin (n + 1)) F)ᵀ ≠ 0 := by
      rw [Matrix.det_transpose]
      exact det_ne_zero k
    have h := HarmonicAnalysis.haarMeasure_map_matrix (Measure.addHaar : Measure F)
      T.normalizedAbsHom hχ μ hM
    rw [Matrix.det_transpose] at h
    have e : (fun x => x ᵥ* (k : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) =
        ⇑(Matrix.toLin' (k : Matrix (Fin (n + 1)) (Fin (n + 1)) F)ᵀ) := by
      funext x
      rw [Matrix.toLin'_apply, Matrix.mulVec_transpose]
    rw [e, h]
  have hdet : IsOpen {g : Langlands.GeneralLinear (n + 1) F |
      normalizedAbsoluteValue T (Matrix.det (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) =
        1} := by
    have e : {g : Langlands.GeneralLinear (n + 1) F |
        normalizedAbsoluteValue T
          (Matrix.det (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) = 1} =
        ((T.determinantNorm (n + 1)).ker : Set (Langlands.GeneralLinear (n + 1) F)) := by
      ext g
      rw [Set.mem_ofPred_eq, SetLike.mem_coe, MonoidHom.mem_ker, ← Units.val_eq_one,
        ← NNReal.coe_eq_one, T.determinantNorm_coe]
      rfl
    rw [e]
    exact T.isOpen_ker_determinantNorm (n + 1)
  have hK₀ : ∃ K₀ : Subgroup (Langlands.GeneralLinear (n + 1) F),
      IsOpen (K₀ : Set (Langlands.GeneralLinear (n + 1) F)) ∧
        IsCompact (K₀ : Set (Langlands.GeneralLinear (n + 1) F)) :=
    ⟨GeneralLinearGroup.integralSubgroup (Fin (n + 1)) T.Integers,
      GeneralLinearGroup.isOpen_integralSubgroup _ _ T.isOpen_integers,
      GeneralLinearGroup.isCompact_integralSubgroup _ _ T.isCompact_integers⟩
  exact ⟨frobeniusEquiv μ (abv := normalizedAbsoluteValue T) (χ := T.normalizedAbsHom)
    (fun _ => rfl) hscale (exists_good hρ hσ hdet hK₀)⟩

end Langlands.AllField.RankinSelberg
