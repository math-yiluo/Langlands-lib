import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.Group.GL.UpperUnipotentEntryCoordinates
import Langlands.HarmonicAnalysis.RectangularFourier
import Mathlib.MeasureTheory.Integral.Prod

/-! # The block Haar formula for the complex upper unipotent group -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

local instance blockUnipotentMeasurable (d : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent d ℂ) := borel _
local instance blockUnipotentBorel (d : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent d ℂ) := ⟨rfl⟩

private def embedUpperEntry (m : ℕ) : UpperEntryPair m ⊕ Fin m → UpperEntryPair (m + 1)
  | Sum.inl i => ⟨(i.val.1.castSucc, i.val.2.castSucc), i.2⟩
  | Sum.inr j => ⟨(j.castSucc, Fin.last m), j.castSucc_lt_last⟩

private def upperEntryBlockEquiv (m : ℕ) : UpperEntryPair m ⊕ Fin m ≃ UpperEntryPair (m + 1) :=
  Equiv.ofBijective (embedUpperEntry m) (by
    constructor
    · intro x y h
      cases x with
      | inl i =>
        cases y with
        | inl j =>
          congr 1
          apply Subtype.ext
          apply Prod.ext <;> apply Fin.ext
          · exact congrArg (fun p : UpperEntryPair (m + 1) => p.val.1.val) h
          · exact congrArg (fun p : UpperEntryPair (m + 1) => p.val.2.val) h
        | inr j =>
          exact False.elim (Fin.castSucc_ne_last i.val.2
            (congrArg (fun p : UpperEntryPair (m + 1) => p.val.2) h))
      | inr i =>
        cases y with
        | inl j =>
          exact False.elim (Fin.castSucc_ne_last j.val.2
            (congrArg (fun p : UpperEntryPair (m + 1) => p.val.2) h.symm))
        | inr j =>
          congr 1
          exact Fin.ext (congrArg (fun p : UpperEntryPair (m + 1) => p.val.1.val) h)
    · intro ij
      rcases ij with ⟨⟨i, j⟩, hij⟩
      have ht : i.val < j.val := hij
      by_cases h : j.val < m
      · let i₀ : Fin m := ⟨i.val, ht.trans h⟩
        let j₀ : Fin m := ⟨j.val, h⟩
        exact ⟨Sum.inl ⟨(i₀, j₀), ht⟩, Subtype.ext (Prod.ext (Fin.ext rfl) (Fin.ext rfl))⟩
      · have hjle : j.val ≤ m := Nat.le_of_lt_succ j.isLt
        have hj : j = Fin.last m := Fin.ext (le_antisymm hjle (Nat.le_of_not_gt h))
        subst j
        exact ⟨Sum.inr ⟨i.val, ht⟩, Subtype.ext (Prod.ext (Fin.ext rfl) rfl)⟩)

private def upperEntryBlockCoordinates (m : ℕ) :
    ((UpperEntryPair m → ℂ) × (Fin m → ℂ)) ≃ᵐ (UpperEntryPair (m + 1) → ℂ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : UpperEntryPair m ⊕ Fin m => ℂ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (upperEntryBlockEquiv m))

private theorem upperEntryBlockCoordinates_left (m : ℕ)
    (x : (UpperEntryPair m → ℂ) × (Fin m → ℂ)) (i : UpperEntryPair m) :
    upperEntryBlockCoordinates m x (embedUpperEntry m (Sum.inl i)) = x.1 i := by
  change MeasurableEquiv.piCongrLeft (fun _ => ℂ) (upperEntryBlockEquiv m)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : UpperEntryPair m ⊕ Fin m => ℂ)).symm x)
    (upperEntryBlockEquiv m (Sum.inl i)) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

private theorem upperEntryBlockCoordinates_right (m : ℕ)
    (x : (UpperEntryPair m → ℂ) × (Fin m → ℂ)) (i : Fin m) :
    upperEntryBlockCoordinates m x (embedUpperEntry m (Sum.inr i)) = x.2 i := by
  change MeasurableEquiv.piCongrLeft (fun _ => ℂ) (upperEntryBlockEquiv m)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : UpperEntryPair m ⊕ Fin m => ℂ)).symm x)
    (upperEntryBlockEquiv m (Sum.inr i)) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

/-- Join the smaller upper-unipotent block and the last column as an element of the
larger upper-unipotent group. -/
def complexUnipotentBlockJoin (m : ℕ) :
    (Langlands.GeneralLinear.upperUnipotent m ℂ × (Fin m → ℂ)) ≃ᵐ
      Langlands.GeneralLinear.upperUnipotent (m + 1) ℂ :=
  (((upperEntryCoordinates m (K := ℂ)).toMeasurableEquiv.prodCongr (MeasurableEquiv.refl _)).trans
    (upperEntryBlockCoordinates m)).trans (upperEntryCoordinates (m + 1) (K := ℂ)).symm.toMeasurableEquiv

/-- The first rows of the joined group element are the rectangle used in the Jacquet recursion. -/
theorem complexUnipotentBlockJoin_rectangle {m : ℕ}
    (u : Langlands.GeneralLinear.upperUnipotent m ℂ) (z : Fin m → ℂ) :
    (fun i : Fin m => (complexUnipotentBlockJoin m (u, z)).val.val i.castSucc) =
      rectangularJoin u.val.val z := by
  ext i j
  refine Fin.lastCases ?_ (fun j₀ => ?_) j
  · rw [rectangularJoin_last]
    change ((upperEntryCoordinates (m + 1) (K := ℂ)).symm
      (upperEntryBlockCoordinates m (upperEntryCoordinates m u, z))).val.val
        i.castSucc (Fin.last m) = _
    rw [upperEntryCoordinates_symm_upper _ i.castSucc_lt_last]
    exact upperEntryBlockCoordinates_right m _ i
  · rw [rectangularJoin_castSucc]
    rcases lt_trichotomy i j₀ with hij | rfl | hji
    · change ((upperEntryCoordinates (m + 1) (K := ℂ)).symm
        (upperEntryBlockCoordinates m (upperEntryCoordinates m u, z))).val.val
          i.castSucc j₀.castSucc = _
      rw [upperEntryCoordinates_symm_upper _ (show i.castSucc < j₀.castSucc from hij)]
      exact (upperEntryBlockCoordinates_left m _ ⟨(i, j₀), hij⟩).trans
        (upperEntryCoordinates_apply u ⟨(i, j₀), hij⟩)
    · rw [UpperUnipotent.entry_diag, UpperUnipotent.entry_diag]
    · rw [UpperUnipotent.entry_eq_zero _ (show j₀.castSucc < i.castSucc from hji),
        UpperUnipotent.entry_eq_zero _ hji]

private def coordinateHaar (ν : AdditiveHaarMeasure ℂ) (d : ℕ) :
    Measure (Langlands.GeneralLinear.upperUnipotent d ℂ) :=
  (upperEntryProductMeasure ν d).map (upperEntryCoordinates d).symm

private theorem measurePreserving_complexUnipotentBlockJoin (ν : AdditiveHaarMeasure ℂ)
    [SigmaFinite ν.measure] (m : ℕ) :
    MeasurePreserving (complexUnipotentBlockJoin m)
      ((coordinateHaar ν m).prod (Measure.pi fun _ : Fin m => ν.measure))
      (coordinateHaar ν (m + 1)) := by
  let μz : Measure (Fin m → ℂ) := Measure.pi fun _ => ν.measure
  let : SFinite (coordinateHaar ν m) := by unfold coordinateHaar; infer_instance
  let e (d : ℕ) := (upperEntryCoordinates d (K := ℂ)).toMeasurableEquiv
  have h (d : ℕ) : MeasurePreserving (e d).symm (upperEntryProductMeasure ν d) (coordinateHaar ν d) :=
    ⟨(e d).symm.measurable, rfl⟩
  have hsplit : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : UpperEntryPair m ⊕ Fin m => ℂ)).symm
      ((upperEntryProductMeasure ν m).prod μz) (Measure.pi fun _ : UpperEntryPair m ⊕ Fin m => ν.measure) :=
    measurePreserving_sumPiEquivProdPi_symm (fun _ : UpperEntryPair m ⊕ Fin m => ν.measure)
  have hcongr : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (upperEntryBlockEquiv m))
      (Measure.pi fun _ : UpperEntryPair m ⊕ Fin m => ν.measure) (upperEntryProductMeasure ν (m + 1)) :=
    measurePreserving_piCongrLeft (fun _ : UpperEntryPair (m + 1) => ν.measure) (upperEntryBlockEquiv m)
  have hprod := (MeasurePreserving.symm (e m).symm (h m)).prod (MeasurePreserving.id μz)
  exact (h (m + 1)).comp (hcongr.comp (hsplit.comp hprod))

variable (m : ℕ) in
/-- The Haar measure in the larger unipotent integral factors through the smaller
unipotent group and the self-dual last-column measure up to one positive scalar. -/
def ComplexLocalUnipotentBlockMeasureStatement : Prop :=
  ∀ (a : ℂˣ) (μH : Measure (Langlands.GeneralLinear.upperUnipotent m ℂ))
    (μG : Measure (Langlands.GeneralLinear.upperUnipotent (m + 1) ℂ)),
    μH.IsHaarMeasure → μG.IsHaarMeasure →
    ∃ c : ℝ≥0, 0 < c ∧ μG =
      c • (μH.prod (Measure.pi fun _ : Fin m => (complexSelfDualMeasure a).measure)).map
        (complexUnipotentBlockJoin m)

theorem complexLocalUnipotentBlockMeasure (m : ℕ) : ComplexLocalUnipotentBlockMeasureStatement m := by
  intro a μH μG hH hG
  let ν := complexSelfDualMeasure a
  let : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  let : μH.IsHaarMeasure := hH
  let : μG.IsHaarMeasure := hG
  let eH := upperEntryCoordinates m (K := ℂ)
  let eG := upperEntryCoordinates (m + 1) (K := ℂ)
  let : LocallyCompactSpace (Langlands.GeneralLinear.upperUnipotent m ℂ) :=
    eH.isClosedEmbedding.locallyCompactSpace
  let : LocallyCompactSpace (Langlands.GeneralLinear.upperUnipotent (m + 1) ℂ) :=
    eG.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology (Langlands.GeneralLinear.upperUnipotent m ℂ) :=
    eH.secondCountableTopology
  let : SecondCountableTopology (Langlands.GeneralLinear.upperUnipotent (m + 1) ℂ) :=
    eG.secondCountableTopology
  let : (coordinateHaar ν m).IsHaarMeasure := upperEntryProductMeasure_isHaar ν
  let : (coordinateHaar ν (m + 1)).IsHaarMeasure := upperEntryProductMeasure_isHaar ν
  let cH := haarScalarFactor μH (coordinateHaar ν m)
  let cG := haarScalarFactor μG (coordinateHaar ν (m + 1))
  have hcH : 0 < cH := haarScalarFactor_pos_of_isHaarMeasure _ _
  have hcG : 0 < cG := haarScalarFactor_pos_of_isHaarMeasure _ _
  let μz : Measure (Fin m → ℂ) := Measure.pi fun _ => ν.measure
  have hμH : μH = cH • coordinateHaar ν m := isMulLeftInvariant_eq_smul _ _
  have hμG : μG = cG • coordinateHaar ν (m + 1) := isMulLeftInvariant_eq_smul _ _
  have hprod : (μH.prod μz).map (complexUnipotentBlockJoin m) = cH • coordinateHaar ν (m + 1) := by
    rw [hμH]
    change (((cH : ℝ≥0∞) • coordinateHaar ν m).prod μz).map (complexUnipotentBlockJoin m) =
      (cH : ℝ≥0∞) • coordinateHaar ν (m + 1)
    rw [Measure.prod_smul_left, Measure.map_smul, (measurePreserving_complexUnipotentBlockJoin ν m).map_eq]
    exact (complexUnipotentBlockJoin m).measurable.aemeasurable
  refine ⟨cG / cH, div_pos hcG hcH, ?_⟩
  change μG = (cG / cH) • (μH.prod μz).map (complexUnipotentBlockJoin m)
  rw [hprod, smul_smul, div_mul_cancel₀ _ hcH.ne', ← hμG]

/-- For an integrable function, the block Haar comparison gives the iterated
smaller-unipotent and last-column integral with the same single scalar. -/
theorem complexLocalUnipotentBlockIntegral (m : ℕ) (a : ℂˣ)
    (μH : Measure (Langlands.GeneralLinear.upperUnipotent m ℂ))
    (μG : Measure (Langlands.GeneralLinear.upperUnipotent (m + 1) ℂ))
    (hH : μH.IsHaarMeasure) (hG : μG.IsHaarMeasure) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : Langlands.GeneralLinear.upperUnipotent (m + 1) ℂ → ℂ,
      Integrable f μG →
      (∫ u, f u ∂μG) = (c : ℂ) *
        ∫ u, ∫ z : Fin m → ℂ, f (complexUnipotentBlockJoin m (u, z))
          ∂Measure.pi (fun _ : Fin m => (complexSelfDualMeasure a).measure) ∂μH := by
  obtain ⟨c, hc, hμ⟩ := complexLocalUnipotentBlockMeasure m a μH μG hH hG
  let e := complexUnipotentBlockJoin m
  let ν := complexSelfDualMeasure a
  let μz : Measure (Fin m → ℂ) := Measure.pi fun _ => ν.measure
  let : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  let : μH.IsHaarMeasure := hH
  let eH := upperEntryCoordinates m (K := ℂ)
  let : LocallyCompactSpace (Langlands.GeneralLinear.upperUnipotent m ℂ) :=
    eH.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology (Langlands.GeneralLinear.upperUnipotent m ℂ) :=
    eH.secondCountableTopology
  refine ⟨c, hc, fun f hf => ?_⟩
  change μG = c • (μH.prod μz).map e at hμ
  have hi : Integrable (f ∘ e) (μH.prod μz) := by
    rw [hμ] at hf
    exact e.measurableEmbedding.integrable_map_iff.mp
      ((integrable_smul_measure (ENNReal.coe_ne_zero.mpr hc.ne') ENNReal.coe_ne_top).mp hf)
  rw [hμ, integral_smul_nnreal_measure, e.measurableEmbedding.integral_map]
  rw [integral_prod (fun p => f (e p)) hi]
  simp only [NNReal.smul_def, Complex.real_smul]
  rfl

/-- The first-superdiagonal sum separates into that of the leading block and the
last adjacent coordinate of the column. -/
theorem complexWhittakerCharacter_blockJoin {m : ℕ} (a : ℂˣ)
    (u : Langlands.GeneralLinear.upperUnipotent (m + 1) ℂ) (z : Fin (m + 1) → ℂ) :
    complexWhittakerCharacter a (complexUnipotentBlockJoin (m + 1) (u, z)).val =
      complexWhittakerCharacter a u.val * (complexScaledCharacter a).complex (z (Fin.last m)) := by
  let U := (complexUnipotentBlockJoin (m + 1) (u, z)).val.val
  have htop (i : Fin m) : U i.castSucc.castSucc i.castSucc.succ = u.val.val i.castSucc i.succ := by
    have hi : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
    rw [hi]
    have h := congrFun (congrFun (complexUnipotentBlockJoin_rectangle u z) i.castSucc)
      i.succ.castSucc
    simpa only [U, rectangularJoin_castSucc] using h
  have hlast : U (Fin.last m).castSucc (Fin.last m).succ = z (Fin.last m) := by
    rw [show (Fin.last m).succ = Fin.last (m + 1) from Fin.ext rfl]
    have h := congrFun (congrFun (complexUnipotentBlockJoin_rectangle u z) (Fin.last m))
      (Fin.last (m + 1))
    simpa only [U, rectangularJoin_last] using h
  unfold complexWhittakerCharacter
  change (complexScaledCharacter a).complex (∑ i : Fin (m + 1), U i.castSucc i.succ) = _
  rw [Fin.sum_univ_castSucc, hlast, AddChar.map_add_eq_mul]
  simp only [htop]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
