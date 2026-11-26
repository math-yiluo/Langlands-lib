import Langlands.Global.RankinSelberg.RealGapAlternateWeighted
import Langlands.Global.RankinSelberg.RealGapUnitDeterminant
import Langlands.Global.RankinSelberg.RealTriangularInversion
import Langlands.Representation.RankinSelberg.AdjacentRankQuotientShear

/-! # Undoing determinant normalization on the two leading real variables -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapNormalizationShear

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (continuous_inverseTranspose inverseTranspose_involutive scalarContinuous)
open Langlands.HarmonicAnalysis (rowMeasure)
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap rightTranslate rightTranslate_mul rightTranslate_one
  continuous_rightTranslate_joint)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal (realSelfDualMeasure RealQuotientMeasureData)
open RealGapAlternateConvergence (alternateGapMeasure)
open RealGapAlternateWeighted (leadingSide)
open RealGapTriangularChart (Outer outerMeasure diagonalWeightMeasure)
open RealGapUnitDeterminant (leadingScalar normalizingScalar normalizationWeight normalizationWeight_eq unitOuterMeasure)
open RealJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "KU" => fun n => unitaryCompact ℝ n
local notation "U" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "Y" => fun q => Fin (q + 1) → ℝ
local notation "Rect" => fun t q => Matrix (Fin (q + 1)) (Fin (t + 1)) ℝ
local notation "Size" => fun t q => t + 1 + q + 1
local notation "Par" => fun t q => Rect t q × (Outer (t + 1) q × U (q + 1))
local notation "Coords" => fun t q => Q t × Par t q

local instance gapNormalizationGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapNormalizationGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapNormalizationMatrixSecondCountable (m n : ℕ) :
    SecondCountableTopology (Matrix (Fin m) (Fin n) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
local instance gapNormalizationGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).isInducing.secondCountableTopology
local instance gapNormalizationGLLocallyCompact (n : ℕ) : LocallyCompactSpace (Langlands.GeneralLinear n ℝ) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).locallyCompactSpace
local instance gapNormalizationUMeasurable (n : ℕ) : MeasurableSpace (U n) := borel _
local instance gapNormalizationUBorel (n : ℕ) : BorelSpace (U n) := ⟨rfl⟩
local instance gapNormalizationQSecondCountable (t : ℕ) : SecondCountableTopology (Q t) :=
  TopologicalSpace.Quotient.secondCountableTopology (leftQuotient_isOpenQuotientMap (U (t + 1))).isOpenMap
local instance gapNormalizationQMeasurable (n : ℕ) : MeasurableSpace (Q n) := borel _
local instance gapNormalizationQBorel (n : ℕ) : BorelSpace (Q n) := ⟨rfl⟩

/-- The leading scalar is continuous in the logarithmic diagonal coordinates. -/
theorem continuous_leadingScalar (k q : ℕ) : Continuous (leadingScalar k q) := by
  unfold leadingScalar
  apply (scalarContinuous (n := k) (R := ℝ)).continuous.comp
  apply (Units.isOpenEmbedding_val (R := ℝ)).isEmbedding.continuous_iff.mpr
  change Continuous (fun y : Y q => Real.exp (-(∑ i, y i) / (k : ℝ)))
  exact Real.continuous_exp.comp ((continuous_finsetSum _ fun i _ => continuous_apply i).neg.div_const _)

private theorem continuous_side (k : ℕ) (dual : Bool) : Continuous (leadingSide (n := k) dual) := by
  cases dual
  · exact continuous_id
  · exact continuous_inverseTranspose k ℝ

private theorem side_involutive {k : ℕ} (dual : Bool) (g : G k) : leadingSide dual (leadingSide dual g) = g := by
  cases dual
  · rfl
  · exact inverseTranspose_involutive k ℝ g

private theorem measurePreserving_side (k : ℕ) (dual : Bool) (η₁ : Measure (G k)) [η₁.IsHaarMeasure] :
    MeasurePreserving (leadingSide (n := k) dual) η₁ η₁ := by
  cases dual
  · exact MeasurePreserving.id _
  · exact Langlands.GodementJacquet.realHaar_measurePreserving_inverseTranspose k η₁

private def leadingChange (k q : ℕ) (dual : Bool) : G k × Y q ≃ᵐ G k × Y q where
  toFun p := ((leadingScalar k q p.2)⁻¹ * leadingSide dual p.1, p.2)
  invFun p := (leadingSide dual (leadingScalar k q p.2 * p.1), p.2)
  left_inv := by
    rintro ⟨g, y⟩
    change (leadingSide dual (leadingScalar k q y * ((leadingScalar k q y)⁻¹ * leadingSide dual g)), y) = _
    rw [mul_inv_cancel_left, side_involutive]
  right_inv := by
    rintro ⟨g, y⟩
    change ((leadingScalar k q y)⁻¹ * leadingSide dual (leadingSide dual (leadingScalar k q y * g)), y) = _
    rw [side_involutive, inv_mul_cancel_left]
  measurable_toFun := (((continuous_leadingScalar k q).inv.measurable.comp measurable_snd).mul
    ((continuous_side k dual).measurable.comp measurable_fst)).prodMk measurable_snd
  measurable_invFun := ((continuous_side k dual).measurable.comp
    (((continuous_leadingScalar k q).measurable.comp measurable_snd).mul measurable_fst)).prodMk measurable_snd

private theorem measurePreserving_leadingChange (k q : ℕ) (dual : Bool) (η₁ : Measure (G k))
    [η₁.IsHaarMeasure] :
    MeasurePreserving (leadingChange k q dual)
      (η₁.prod (diagonalWeightMeasure k q))
      (η₁.prod (diagonalWeightMeasure k q)) := by
  let ξ := η₁
  let η := diagonalWeightMeasure k q
  let e := leadingChange k q dual
  refine ⟨e.measurable, ?_⟩
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf e.measurable]
  change (∫⁻ p, (f ∘ e) p ∂ξ.prod η) = ∫⁻ p, f p ∂ξ.prod η
  rw [lintegral_prod_symm' _ (hf.comp e.measurable), lintegral_prod_symm' _ hf]
  refine lintegral_congr fun y => ?_
  let g := fun z : G k => f (z, y)
  let m := fun z : G k => (leadingScalar k q y)⁻¹ * leadingSide dual z
  have hg : Measurable g := hf.comp (measurable_id.prodMk measurable_const)
  have hm : MeasurePreserving m ξ ξ :=
    (measurePreserving_mul_left ξ (leadingScalar k q y)⁻¹).comp (measurePreserving_side k dual η₁)
  change ∫⁻ z, g (m z) ∂ξ = ∫⁻ z, g z ∂ξ
  rw [← lintegral_map hg hm.measurable, hm.map_eq]

/-- The leading change of coordinates in the outer triangular chart. -/
def outerChange (k q : ℕ) (dual : Bool) : Outer k q ≃ᵐ Outer k q :=
  ((leadingChange k q dual).prodCongr (MeasurableEquiv.refl _)).prodCongr (MeasurableEquiv.refl _)

@[simp]
theorem outerChange_apply (k q : ℕ) (dual : Bool) (p : Outer k q) :
    outerChange k q dual p =
      ((((leadingScalar k q p.1.1.2)⁻¹ * leadingSide dual p.1.1.1, p.1.1.2), p.1.2), p.2) := rfl

private def scalarOnPar (t q : ℕ) (p : Par t q) : G (t + 1) := leadingScalar (t + 1) q p.2.1.1.1.2

private theorem measurable_scalarOnPar (t q : ℕ) : Measurable (scalarOnPar t q) :=
  (continuous_leadingScalar (t + 1) q).measurable.comp
    (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_snd))))

private def quotientChange (t q : ℕ) : Coords t q ≃ᵐ Coords t q where
  toFun p := (rightTranslate (U (t + 1)) (scalarOnPar t q p.2) p.1, p.2)
  invFun p := (rightTranslate (U (t + 1)) (scalarOnPar t q p.2)⁻¹ p.1, p.2)
  left_inv := by
    rintro ⟨g, p⟩
    change (rightTranslate (U (t + 1)) (scalarOnPar t q p)⁻¹
      (rightTranslate (U (t + 1)) (scalarOnPar t q p) g), p) = _
    rw [rightTranslate_mul, mul_inv_cancel, rightTranslate_one]
  right_inv := by
    rintro ⟨g, p⟩
    change (rightTranslate (U (t + 1)) (scalarOnPar t q p)
      (rightTranslate (U (t + 1)) (scalarOnPar t q p)⁻¹ g), p) = _
    rw [rightTranslate_mul, inv_mul_cancel, rightTranslate_one]
  measurable_toFun := ((continuous_rightTranslate_joint (U (t + 1))).measurable.comp
    (measurable_fst.prodMk ((measurable_scalarOnPar t q).comp measurable_snd))).prodMk measurable_snd
  measurable_invFun := ((continuous_rightTranslate_joint (U (t + 1))).measurable.comp
    (measurable_fst.prodMk ((measurable_scalarOnPar t q).inv.comp measurable_snd))).prodMk measurable_snd

private theorem measurePreserving_quotientChange (t q : ℕ) (D : RealQuotientMeasureData t)
    (η : Measure (Par t q)) [SFinite η] :
    MeasurePreserving (quotientChange t q) (D.measure.prod η) (D.measure.prod η) := by
  let e := leftQuotient_isOpenQuotientMap (U (t + 1))
  let : SigmaCompactSpace (G (t + 1)) := sigmaCompactSpace_of_locallyCompact_secondCountable
  let : SigmaCompactSpace (Q t) := by
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr e.surjective]
    exact isSigmaCompact_range e.continuous
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let E := quotientChange t q
  refine ⟨E.measurable, ?_⟩
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf E.measurable]
  change (∫⁻ p, (f ∘ E) p ∂D.measure.prod η) = ∫⁻ p, f p ∂D.measure.prod η
  rw [lintegral_prod_symm' _ (hf.comp E.measurable), lintegral_prod_symm' _ hf]
  refine lintegral_congr fun p => ?_
  let g := fun x : Q t => f (x, p)
  have hg : Measurable g := hf.comp (measurable_id.prodMk measurable_const)
  have h := D.compatible.right_invariant (scalarOnPar t q p)
  change ∫⁻ x, g (rightTranslate (U (t + 1)) (scalarOnPar t q p) x) ∂D.measure = ∫⁻ x, g x ∂D.measure
  rw [← lintegral_map hg h.measurable, h.map_eq]

/-- Map the unnormalized coordinates to the two leading coordinates of the normalized integral. -/
def normalizationShear (t q : ℕ) (dual : Bool) : Coords t q ≃ᵐ Coords t q :=
  (quotientChange t q).trans ((MeasurableEquiv.refl _).prodCongr
    ((MeasurableEquiv.refl _).prodCongr ((outerChange (t + 1) q dual).prodCongr (MeasurableEquiv.refl _))))

@[simp]
theorem normalizationShear_apply (t q : ℕ) (dual : Bool) (x : Coords t q) :
    normalizationShear t q dual x =
      (rightTranslate (U (t + 1)) (leadingScalar (t + 1) q x.2.2.1.1.1.2) x.1,
        x.2.1, outerChange (t + 1) q dual x.2.2.1, x.2.2.2) := rfl

/-- The shear preserves the exact unnormalized product measure on both sides. -/
def RealGapNormalizationShearStatement : Prop :=
  ∀ (t q : ℕ) (a : ℝˣ) (D : RealQuotientMeasureData t) (νY : Measure (Rect t q))
    (η₁ : Measure (G (t + 1))) (κ : Measure (KU (Size t q))),
    η₁.IsHaarMeasure → κ.IsHaarMeasure → SigmaFinite νY → ∀ dual : Bool,
    MeasurePreserving (normalizationShear t q dual) (alternateGapMeasure t q a D νY η₁ κ)
      (alternateGapMeasure t q a D νY η₁ κ)

set_option maxHeartbeats 850000 in
theorem realGapNormalizationShear : RealGapNormalizationShearStatement := by
  intro t q a D νY η₁ κ hη₁ hκ hνY dual
  let k := t + 1
  let μ := realSelfDualMeasure a
  let η := entryHaar μ (q + 1)
  let : η₁.IsHaarMeasure := hη₁
  let σ := outerMeasure k q μ η₁ κ
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let : κ.IsHaarMeasure := hκ
  let : SigmaFinite νY := hνY
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite κ := inferInstance
  let : SigmaFinite η := entryHaar_sigmaFinite μ _
  let : SigmaFinite σ := inferInstanceAs (SigmaFinite
    (((η₁.prod (diagonalWeightMeasure k q)).prod κ).prod (rowMeasure μ k)))
  let : SigmaFinite (σ.prod η) := inferInstance
  let : SigmaFinite (νY.prod (σ.prod η)) := inferInstance
  let : SigmaCompactSpace (G (t + 1)) := sigmaCompactSpace_of_locallyCompact_secondCountable
  let : SigmaCompactSpace (Q t) := by
    let e := leftQuotient_isOpenQuotientMap (U (t + 1))
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr e.surjective]
    exact isSigmaCompact_range e.continuous
  have ho : MeasurePreserving (outerChange k q dual) σ σ :=
    ((measurePreserving_leadingChange k q dual η₁).prod (MeasurePreserving.id κ)).prod
      (MeasurePreserving.id (rowMeasure μ k))
  have hleft := measurePreserving_quotientChange t q D (νY.prod (σ.prod η))
  exact ((MeasurePreserving.id D.measure).prod ((MeasurePreserving.id νY).prod
    (ho.prod (MeasurePreserving.id η)))).comp hleft

end Langlands.Global.RankinSelbergGlobal.RealGapNormalizationShear
