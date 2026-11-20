import Langlands.Group.GL.UpperUnipotentEntryCoordinates
import Langlands.Representation.Archimedean.ComplexPartialJacquet
import Langlands.Representation.Shahidi.UnipotentProduct
import Langlands.Representation.Whittaker.DualTransform

/-! # Entry-product Haar for complex open-cell Jacquet integrals -/

noncomputable section

open MeasureTheory
open scoped Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetUnipotentMeasure

open GeneralLinear (UpperEntryPair upperEntryCoordinates upperEntryProductMeasure
  upperEntryCoordinates_apply upperEntryProductMeasure_isHaar weylLong_conjugate_entry
  inverseTranspose_entry)
open HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)
open Langlands.Shahidi (unipotentProduct unipotentProductMeasure)
open Langlands.Archimedean.ComplexPartialJacquet (vecMulEquiv vecMulEquiv_apply map_vecMulEquiv)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (det_upperUnipotent)

local notation "N" => GeneralLinear.upperUnipotent

local instance jacquetUnipotentMeasurable (m : ℕ) : MeasurableSpace (N m ℂ) := borel _
local instance jacquetUnipotentBorel (m : ℕ) : BorelSpace (N m ℂ) := ⟨rfl⟩

/-- Product of the supplied scalar measure on the actual strictly upper entries. -/
def entryHaar (μ : AdditiveHaarMeasure ℂ) (m : ℕ) : Measure (N m ℂ) :=
  (upperEntryProductMeasure μ m).map (upperEntryCoordinates m).symm

theorem entryHaar_isHaar (μ : AdditiveHaarMeasure ℂ) (m : ℕ) : (entryHaar μ m).IsHaarMeasure := by
  have : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  have : SigmaFinite μ.measure := inferInstance
  exact upperEntryProductMeasure_isHaar μ

theorem entryHaar_sigmaFinite (μ : AdditiveHaarMeasure ℂ) (m : ℕ) :
    SigmaFinite (entryHaar μ m) := by
  have : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  have : SigmaFinite μ.measure := inferInstance
  exact (upperEntryCoordinates (K := ℂ) m).symm.toMeasurableEquiv.sigmaFinite_map

private theorem measurePreserving_fromEntries (μ : AdditiveHaarMeasure ℂ) (m : ℕ) :
    MeasurePreserving (upperEntryCoordinates (K := ℂ) m).symm.toMeasurableEquiv
      (upperEntryProductMeasure μ m) (entryHaar μ m) :=
  ⟨(upperEntryCoordinates (K := ℂ) m).symm.measurable, rfl⟩

private def lastColumnIndex (m : ℕ) : UpperEntryPair m ⊕ Fin m → UpperEntryPair (m + 1)
  | .inl ij => ⟨(ij.1.1.castSucc, ij.1.2.castSucc), Fin.castSucc_lt_castSucc_iff.mpr ij.2⟩
  | .inr i => ⟨(i.castSucc, Fin.last m), Fin.castSucc_lt_last i⟩

private theorem lastColumnIndex_bijective (m : ℕ) : Function.Bijective (lastColumnIndex m) := by
  constructor
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        exact congrArg Sum.inl (Subtype.ext (Prod.ext
          (Fin.castSucc_inj.mp (congrArg (fun p => p.val.1) h))
          (Fin.castSucc_inj.mp (congrArg (fun p => p.val.2) h))))
      | inr y => exact (Fin.castSucc_ne_last _ (congrArg (fun p => p.val.2) h)).elim
    | inr x =>
      cases y with
      | inl y => exact (Fin.castSucc_ne_last _ (congrArg (fun p => p.val.2) h.symm)).elim
      | inr y => exact congrArg Sum.inr (Fin.castSucc_inj.mp (congrArg (fun p => p.val.1) h))
  · rintro ⟨⟨i, j⟩, hij⟩
    induction i using Fin.lastCases with
    | last => exact (not_lt_of_ge (Fin.le_last j) hij).elim
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact ⟨.inr i, rfl⟩
      | cast j => exact ⟨.inl ⟨(i, j), Fin.castSucc_lt_castSucc_iff.mp hij⟩, rfl⟩

private def lastColumnIndexEquiv (m : ℕ) : UpperEntryPair m ⊕ Fin m ≃ UpperEntryPair (m + 1) :=
  Equiv.ofBijective (lastColumnIndex m) (lastColumnIndex_bijective m)

private theorem constPiCongrLeft_apply {I J : Type} (e : I ≃ J) (x : I → ℂ) (j : J) :
    MeasurableEquiv.piCongrLeft (fun _ => ℂ) e x j = x (e.symm j) := by
  simpa only [e.apply_symm_apply] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℂ) e x (e.symm j))

private def splitEntries (m : ℕ) : (UpperEntryPair (m + 1) → ℂ) ≃ᵐ
    (UpperEntryPair m → ℂ) × (Fin m → ℂ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (lastColumnIndexEquiv m).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ))

private def lastColumnSplit (m : ℕ) : (N (m + 1) ℂ) ≃ᵐ (N m ℂ) × (Fin m → ℂ) :=
  (upperEntryCoordinates (K := ℂ) (m + 1)).toMeasurableEquiv.trans ((splitEntries m).trans
    ((upperEntryCoordinates (K := ℂ) m).symm.toMeasurableEquiv.prodCongr
      (MeasurableEquiv.refl (Fin m → ℂ))))

private theorem measurePreserving_lastColumnSplit (μ : AdditiveHaarMeasure ℂ) (m : ℕ) :
    MeasurePreserving (lastColumnSplit m) (entryHaar μ (m + 1))
      ((entryHaar μ m).prod (rowMeasure μ m)) := by
  have : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  have : SigmaFinite μ.measure := inferInstance
  have hsplit : MeasurePreserving (splitEntries m) (upperEntryProductMeasure μ (m + 1))
      ((upperEntryProductMeasure μ m).prod (rowMeasure μ m)) := by
    exact (measurePreserving_piCongrLeft (fun _ => μ.measure) (lastColumnIndexEquiv m).symm).trans
      (measurePreserving_sumPiEquivProdPi (fun _ => μ.measure))
  have hlast : MeasurePreserving
      ((upperEntryCoordinates (K := ℂ) m).symm.toMeasurableEquiv.prodCongr
        (MeasurableEquiv.refl (Fin m → ℂ)))
      ((upperEntryProductMeasure μ m).prod (rowMeasure μ m))
      ((entryHaar μ m).prod (rowMeasure μ m)) :=
    (measurePreserving_fromEntries μ m).prod (MeasurePreserving.id (rowMeasure μ m))
  exact ((measurePreserving_fromEntries μ (m + 1)).symm _).trans
    (hsplit.trans hlast)

private theorem lastColumnSplit_product {m : ℕ} (u : N m ℂ) (v : Fin m → ℂ) :
    lastColumnSplit m (unipotentProduct (u, v)) = (u, u.val.val *ᵥ v) := by
  apply Prod.ext
  · apply (upperEntryCoordinates m (K := ℂ)).injective
    funext ij
    change upperEntryCoordinates m ((upperEntryCoordinates m).symm
      (fun i => MeasurableEquiv.piCongrLeft (fun _ => ℂ) (lastColumnIndexEquiv m).symm
        (upperEntryCoordinates (m + 1) (unipotentProduct (u, v))) (.inl i))) ij = _
    rw [(upperEntryCoordinates m).apply_symm_apply, constPiCongrLeft_apply]
    change upperEntryCoordinates _ (unipotentProduct (u, v)) (lastColumnIndex m (.inl ij)) = _
    simp only [lastColumnIndex, upperEntryCoordinates_apply, Langlands.Shahidi.unipotentProduct_left]
  · funext i
    change MeasurableEquiv.piCongrLeft (fun _ => ℂ) (lastColumnIndexEquiv m).symm
      (upperEntryCoordinates (m + 1) (unipotentProduct (u, v))) (.inr i) = _
    rw [constPiCongrLeft_apply]
    change upperEntryCoordinates (m + 1) (unipotentProduct (u, v)) (lastColumnIndex m (.inr i)) = _
    simp only [lastColumnIndex, upperEntryCoordinates_apply, Langlands.Shahidi.unipotentProduct_column]

private theorem measurePreserving_unipotentMulVec (μ : AdditiveHaarMeasure ℂ) {m : ℕ}
    (u : N m ℂ) [SigmaFinite μ.measure] :
    MeasurePreserving (u.val.val.mulVec) (rowMeasure μ m) (rowMeasure μ m) := by
  have hdet : u.val.val.transpose.det = 1 := by rw [Matrix.det_transpose, det_upperUnipotent]
  let e := vecMulEquiv (hdet ▸ one_ne_zero)
  have he : (e : (Fin m → ℂ) → (Fin m → ℂ)) = u.val.val.mulVec := by
    funext v
    rw [vecMulEquiv_apply, Matrix.vecMul_transpose]
  rw [← he]
  refine ⟨e.measurable, ?_⟩
  rw [Measure.isAddLeftInvariant_eq_smul (rowMeasure μ m) volume,
    Measure.map_smul _ e.measurable.aemeasurable, map_vecMulEquiv]
  simp [hdet]

/-- The ordered upper-left/last-column product has the exact scalar entry normalization. -/
theorem unipotentProductMeasure_entryHaar (μ : AdditiveHaarMeasure ℂ) (m : ℕ) :
    unipotentProductMeasure (entryHaar μ m) (rowMeasure μ m) = entryHaar μ (m + 1) := by
  have : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  have : SigmaFinite μ.measure := inferInstance
  have : SigmaFinite (entryHaar μ m) := entryHaar_sigmaFinite μ m
  have hs : MeasurePreserving (fun p : (N m ℂ) × (Fin m → ℂ) => (p.1, p.1.val.val *ᵥ p.2))
      ((entryHaar μ m).prod (rowMeasure μ m)) ((entryHaar μ m).prod (rowMeasure μ m)) := by
    apply (MeasurePreserving.id (entryHaar μ m)).skew_product
      (g := fun (u : N m ℂ) (v : Fin m → ℂ) => u.val.val *ᵥ v)
    · apply Continuous.measurable
      exact ((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).matrix_mulVec
        continuous_snd
    · exact ae_of_all _ fun u => (measurePreserving_unipotentMulVec μ u).map_eq
  have hp := ((measurePreserving_lastColumnSplit μ m).symm _).comp hs
  have he : (lastColumnSplit m).symm ∘ (fun p : (N m ℂ) × (Fin m → ℂ) => (p.1, p.1.val.val *ᵥ p.2)) =
      unipotentProduct := by
    funext p
    exact (MeasurableEquiv.symm_apply_eq _).mpr (lastColumnSplit_product p.1 p.2).symm
  rw [he] at hp
  exact hp.map_eq

private def revPair (m : ℕ) : UpperEntryPair m ≃ UpperEntryPair m where
  toFun ij := ⟨(ij.1.2.rev, ij.1.1.rev), Fin.rev_lt_rev.mpr ij.2⟩
  invFun ij := ⟨(ij.1.2.rev, ij.1.1.rev), Fin.rev_lt_rev.mpr ij.2⟩
  left_inv ij := Subtype.ext (Prod.ext (Fin.rev_rev ij.1.1) (Fin.rev_rev ij.1.2))
  right_inv ij := Subtype.ext (Prod.ext (Fin.rev_rev ij.1.1) (Fin.rev_rev ij.1.2))

/-- Reflection of the strictly upper entries across the antidiagonal. -/
def transposeReflection (m : ℕ) : N m ℂ ≃ᵐ N m ℂ :=
  let e := (upperEntryCoordinates (K := ℂ) m).toMeasurableEquiv
  e.trans ((MeasurableEquiv.piCongrLeft (fun _ => ℂ) (revPair m)).trans e.symm)

/-- In matrix coordinates the reflection transposes and conjugates by the long Weyl element. -/
theorem transposeReflection_eq (r : ℕ) (u : N (r + 1) ℂ) :
    transposeReflection (r + 1) u = Whittaker.reflectedUnipotent u⁻¹ := by
  let e := upperEntryCoordinates (K := ℂ) (r + 1)
  apply e.injective
  funext ij
  change e (e.symm (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (revPair (r + 1)) (e u))) ij = _
  rw [e.apply_symm_apply, constPiCongrLeft_apply]
  simp only [e, upperEntryCoordinates_apply, Whittaker.reflectedUnipotent_val,
    weylLong_conjugate_entry, inverseTranspose_entry, Subgroup.coe_inv, inv_inv]
  rfl

theorem measurePreserving_transposeReflection (μ : AdditiveHaarMeasure ℂ) (m : ℕ) :
    MeasurePreserving (transposeReflection m) (entryHaar μ m) (entryHaar μ m) := by
  have : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  have : SigmaFinite μ.measure := inferInstance
  unfold transposeReflection
  exact ((measurePreserving_fromEntries μ m).symm _).trans
    ((measurePreserving_piCongrLeft (fun _ => μ.measure) (revPair m)).trans
      (measurePreserving_fromEntries μ m))

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetUnipotentMeasure
