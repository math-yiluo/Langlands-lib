import Langlands.Representation.Shahidi.IwasawaMeasures
import Langlands.Group.GL.UpperBruhatEmbedding
import Langlands.Group.GL.UpperUnipotent
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular

/-! # The actual unipotent product in Shahidi's measure item 1 -/

noncomputable section

namespace Langlands.Shahidi

open GeneralLinear MeasureTheory
open scoped Matrix

universe uF
variable {F : Type uF} [Field F] {n : ℕ}

@[simp] theorem lastColumnUnipotent_left (x : Fin n → F) (i j : Fin n) :
    lastColumnUnipotent n x i.castSucc j.castSucc = (1 : Matrix (Fin n) (Fin n) F) i j := by
  change Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (fun i (_ : Fin 1) => x i)
    0 1 (finSumFinEquiv.symm (i.castAdd 1)) (finSumFinEquiv.symm (j.castAdd 1)) = _
  simp
  rfl

@[simp] theorem lastColumnUnipotent_bottom_left (x : Fin n → F) (j : Fin n) :
    lastColumnUnipotent n x (Fin.last n) j.castSucc = 0 := by
  change Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (fun i (_ : Fin 1) => x i)
    0 1 (finSumFinEquiv.symm ((0 : Fin 1).natAdd n)) (finSumFinEquiv.symm (j.castAdd 1)) = _
  simp
  rfl

@[simp] theorem lastColumnUnipotent_bottom_right (x : Fin n → F) :
    lastColumnUnipotent n x (Fin.last n) (Fin.last n) = 1 := by
  change Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (fun i (_ : Fin 1) => x i)
    0 1 (finSumFinEquiv.symm ((0 : Fin 1).natAdd n))
      (finSumFinEquiv.symm ((0 : Fin 1).natAdd n)) = _
  simp
  change (1 : Matrix (Fin 1) (Fin 1) F) 0 0 = 1
  simp

@[simp] theorem lastColumnUnipotent_column (x : Fin n → F) (i : Fin n) :
    lastColumnUnipotent n x i.castSucc (Fin.last n) = x i :=
  lastColumnUnipotent_entry n x i

/-- The additive column coordinates belong to the actual full upper-unipotent group. -/
def lastColumnUpper (x : Fin n → F) : upperUnipotent (n + 1) F :=
  ⟨lastColumnUnipotent n x, by
    constructor
    · intro i j hji
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact False.elim (lt_irrefl _ hji)
        | cast j => exact lastColumnUnipotent_bottom_left x j
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact False.elim (not_lt_of_ge (Fin.le_last _) hji)
        | cast j => rw [lastColumnUnipotent_left, Matrix.one_apply_ne]
                    exact ne_of_gt (Fin.castSucc_lt_castSucc_iff.mp hji)
    · intro i
      induction i using Fin.lastCases with
      | last => exact lastColumnUnipotent_bottom_right x
      | cast i => simp⟩

/-- Embed the smaller upper-unipotent group in the upper-left block. -/
def upperLeftUnipotent (u : upperUnipotent n F) : upperUnipotent (n + 1) F :=
  ⟨Bruhat.insert (Fin.last n) u.val, by
    constructor
    · exact Bruhat.insert_upper _ _ u.property.1
    · intro i
      induction i using Fin.succAboveCases (Fin.last n) with
      | x => exact Bruhat.insert_p_p _ _
      | p i => rw [Bruhat.insert_succAbove_succAbove]; exact u.property.2 i⟩

@[simp] theorem upperLeftUnipotent_left (u : upperUnipotent n F) (i j : Fin n) :
    (upperLeftUnipotent u).val i.castSucc j.castSucc = u.val i j := by
  simpa only [upperLeftUnipotent, Fin.succAbove_last] using Bruhat.insert_succAbove_succAbove (Fin.last n) u.val i j

@[simp] theorem upperLeftUnipotent_column (u : upperUnipotent n F) (i : Fin n) :
    (upperLeftUnipotent u).val i.castSucc (Fin.last n) = 0 := by
  simpa only [upperLeftUnipotent, Fin.succAbove_last] using Bruhat.insert_succAbove_p (Fin.last n) u.val i

@[simp] theorem upperLeftUnipotent_bottom (u : upperUnipotent n F) (j : Fin n) :
    (upperLeftUnipotent u).val (Fin.last n) j.castSucc = 0 := by
  simpa only [upperLeftUnipotent, Fin.succAbove_last] using Bruhat.insert_p_succAbove (Fin.last n) u.val j

@[simp] theorem upperLeftUnipotent_corner (u : upperUnipotent n F) :
    (upperLeftUnipotent u).val (Fin.last n) (Fin.last n) = 1 :=
  Bruhat.insert_p_p _ _

/-- The source order is `diag(u,1) * u(x)`, not its reverse. -/
def unipotentProduct (p : upperUnipotent n F × (Fin n → F)) : upperUnipotent (n + 1) F :=
  upperLeftUnipotent p.1 * lastColumnUpper p.2

@[simp] theorem unipotentProduct_left (u : upperUnipotent n F) (x : Fin n → F)
    (i j : Fin n) : (unipotentProduct (u,x)).val i.castSucc j.castSucc = u.val i j := by
  change ((upperLeftUnipotent u).val.val * (lastColumnUnipotent n x).val) _ _ = _
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [upperLeftUnipotent_left, lastColumnUnipotent_left,
    upperLeftUnipotent_column, zero_mul, add_zero]
  change (u.val.val * (1 : Matrix (Fin n) (Fin n) F)) i j = _
  rw [Matrix.mul_one]

@[simp] theorem unipotentProduct_column (u : upperUnipotent n F) (x : Fin n → F)
    (i : Fin n) : (unipotentProduct (u,x)).val i.castSucc (Fin.last n) =
      (u.val.val *ᵥ x) i := by
  change ((upperLeftUnipotent u).val.val * (lastColumnUnipotent n x).val) _ _ = _
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [upperLeftUnipotent_left, lastColumnUnipotent_column,
    upperLeftUnipotent_column, zero_mul, add_zero]
  rfl

/-- The upper-left block of an upper-unipotent matrix, with its actual inverse block. -/
def unipotentUpperLeft (u : upperUnipotent (n + 1) F) : upperUnipotent n F :=
  ⟨{ val := (fun i j => u.val i.castSucc j.castSucc : Matrix (Fin n) (Fin n) F)
     inv := (fun i j => u.val.inv i.castSucc j.castSucc : Matrix (Fin n) (Fin n) F)
     val_inv := by
       ext i j
       change (∑ k : Fin n, u.val i.castSucc k.castSucc * u.val.inv k.castSucc j.castSucc) =
         (1 : Matrix (Fin n) (Fin n) F) i j
       have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) F =>
         M i.castSucc j.castSucc) u.val.val_inv
       have hz : u.val.inv (Fin.last n) j.castSucc = 0 :=
         UpperUnipotent.entry_eq_zero (u⁻¹) (Fin.castSucc_lt_last j)
       rw [Matrix.mul_apply, Fin.sum_univ_castSucc, hz, mul_zero, add_zero] at h
       simpa only [Matrix.one_apply, Fin.castSucc_inj] using h
     inv_val := by
       ext i j
       change (∑ k : Fin n, u.val.inv i.castSucc k.castSucc * u.val k.castSucc j.castSucc) =
         (1 : Matrix (Fin n) (Fin n) F) i j
       have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) F =>
         M i.castSucc j.castSucc) u.val.inv_val
       rw [Matrix.mul_apply, Fin.sum_univ_castSucc,
         UpperUnipotent.entry_eq_zero u (Fin.castSucc_lt_last j), mul_zero, add_zero] at h
       simpa only [Matrix.one_apply, Fin.castSucc_inj] using h },
   ⟨fun _ _ h => u.property.1 h, fun i => u.property.2 i.castSucc⟩⟩

/-- Recover the product coordinates; the column is multiplied by the inverse smaller block. -/
def unipotentProductCoordinates (u : upperUnipotent (n + 1) F) :
    upperUnipotent n F × (Fin n → F) :=
  (unipotentUpperLeft u, (unipotentUpperLeft u).val.inv *ᵥ
    (fun i => u.val i.castSucc (Fin.last n)))

@[simp] theorem unipotentUpperLeft_product (u : upperUnipotent n F) (x : Fin n → F) :
    unipotentUpperLeft (unipotentProduct (u,x)) = u := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact unipotentProduct_left u x i j

@[simp] theorem unipotentProductCoordinates_product (p : upperUnipotent n F × (Fin n → F)) :
    unipotentProductCoordinates (unipotentProduct p) = p := by
  rcases p with ⟨u,x⟩
  apply Prod.ext
  · exact unipotentUpperLeft_product u x
  · change (unipotentUpperLeft (unipotentProduct (u,x))).val.inv *ᵥ
      (fun i => (unipotentProduct (u,x)).val i.castSucc (Fin.last n)) = x
    rw [unipotentUpperLeft_product]
    simp only [unipotentProduct_column]
    rw [Matrix.mulVec_mulVec, u.val.inv_val, Matrix.one_mulVec]

@[simp] theorem unipotentProduct_coordinates (u : upperUnipotent (n + 1) F) :
    unipotentProduct (unipotentProductCoordinates u) = u := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact (UpperUnipotent.entry_diag _ _).trans (UpperUnipotent.entry_diag _ _).symm
    | cast j => rw [UpperUnipotent.entry_eq_zero _ (Fin.castSucc_lt_last j),
        UpperUnipotent.entry_eq_zero _ (Fin.castSucc_lt_last j)]
  | cast i =>
    induction j using Fin.lastCases with
    | cast j => exact unipotentProduct_left _ _ i j
    | last =>
      change (unipotentProduct (unipotentUpperLeft u, _)).val i.castSucc (Fin.last n) = _
      rw [unipotentProduct_column, Matrix.mulVec_mulVec,
        (unipotentUpperLeft u).val.val_inv, Matrix.one_mulVec]

/-- The ordered multiplication is a genuine bijection of the actual groups as spaces.
It is not claimed to be a homomorphism from the direct product group. -/
def unipotentProductEquiv :
    (upperUnipotent n F × (Fin n → F)) ≃ upperUnipotent (n + 1) F where
  toFun := unipotentProduct
  invFun := unipotentProductCoordinates
  left_inv := unipotentProductCoordinates_product
  right_inv := unipotentProduct_coordinates

section Topology
variable [TopologicalSpace F] [IsTopologicalRing F]

private theorem continuous_upperLeftUnipotent :
    Continuous (upperLeftUnipotent (F := F) (n := n)) := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · apply continuous_matrix
    intro i j
    induction i using Fin.succAboveCases (Fin.last n) with
    | x =>
      induction j using Fin.succAboveCases (Fin.last n) with
      | x => simpa only [Function.comp_def, UpperUnipotent.entry, ContinuousMap.coe_mk, upperLeftUnipotent, Bruhat.insert_p_p] using
          (continuous_const : Continuous (fun _ : upperUnipotent n F => (1 : F)))
      | p j => simpa only [Function.comp_def, UpperUnipotent.entry, ContinuousMap.coe_mk, upperLeftUnipotent, Bruhat.insert_p_succAbove] using
          (continuous_const : Continuous (fun _ : upperUnipotent n F => (0 : F)))
    | p i =>
      induction j using Fin.succAboveCases (Fin.last n) with
      | x => simpa only [Function.comp_def, UpperUnipotent.entry, ContinuousMap.coe_mk, upperLeftUnipotent, Bruhat.insert_succAbove_p] using
          (continuous_const : Continuous (fun _ : upperUnipotent n F => (0 : F)))
      | p j =>
        simp only [Function.comp_def, Bruhat.insert_succAbove_succAbove]
        exact (UpperUnipotent.entry (R := F) i j).continuous
  · change Continuous (fun u : upperUnipotent n F =>
      (Bruhat.insert (Fin.last n) u.val).inv)
    have he : (fun u : upperUnipotent n F => (Bruhat.insert (Fin.last n) u.val).inv) =
        fun u => (Bruhat.insert (Fin.last n) (u⁻¹).val).val := by
      funext u
      exact congrArg Units.val ((Bruhat.insert (Fin.last n)).map_inv u.val).symm
    rw [he]
    apply continuous_matrix
    intro i j
    induction i using Fin.succAboveCases (Fin.last n) with
    | x =>
      induction j using Fin.succAboveCases (Fin.last n) with
      | x => simpa only [Bruhat.insert_p_p] using
          (continuous_const : Continuous (fun _ : upperUnipotent n F => (1 : F)))
      | p j => simpa only [Bruhat.insert_p_succAbove] using
          (continuous_const : Continuous (fun _ : upperUnipotent n F => (0 : F)))
    | p i =>
      induction j using Fin.succAboveCases (Fin.last n) with
      | x => simpa only [Bruhat.insert_succAbove_p] using
          (continuous_const : Continuous (fun _ : upperUnipotent n F => (0 : F)))
      | p j =>
        simp only [Bruhat.insert_succAbove_succAbove]
        exact (UpperUnipotent.entry (R := F) i j).continuous.comp continuous_inv

theorem continuous_unipotentProduct :
    Continuous (unipotentProduct (F := F) (n := n)) :=
  (continuous_upperLeftUnipotent.comp continuous_fst).mul
    (((continuous_lastColumnUnipotent n).subtype_mk _).comp continuous_snd)

private theorem continuous_unipotentUpperLeft :
    Continuous (unipotentUpperLeft (F := F) (n := n)) := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · exact continuous_matrix fun i j =>
      (UpperUnipotent.entry (R := F) i.castSucc j.castSucc).continuous
  · exact continuous_matrix fun i j =>
      ((UpperUnipotent.entry (R := F) i.castSucc j.castSucc).continuous.comp continuous_inv)

theorem continuous_unipotentProductCoordinates :
    Continuous (unipotentProductCoordinates (F := F) (n := n)) := by
  apply continuous_unipotentUpperLeft.prodMk
  apply Continuous.matrix_mulVec
  · exact Units.continuous_coe_inv.comp
      (continuous_subtype_val.comp continuous_unipotentUpperLeft)
  · exact continuous_pi fun i =>
      (UpperUnipotent.entry (R := F) i.castSucc (Fin.last n)).continuous

/-- The genuine coordinate homeomorphism for `N_n × F^n → N_(n+1)`. -/
def unipotentProductHomeomorph :
    (upperUnipotent n F × (Fin n → F)) ≃ₜ upperUnipotent (n + 1) F where
  toEquiv := unipotentProductEquiv
  continuous_toFun := continuous_unipotentProduct
  continuous_invFun := continuous_unipotentProductCoordinates

end Topology

section Measures
variable [MeasurableSpace F] [MeasurableSpace (upperUnipotent n F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)]

/-- The actual ordered product measure `dn₁ dn₂` on the full upper-unipotent group. -/
def unipotentProductMeasure (dn₁ : Measure (upperUnipotent n F))
    (dn₂ : Measure (Fin n → F)) : Measure (upperUnipotent (n + 1) F) :=
  Measure.map unipotentProduct (dn₁.prod dn₂)

/-- The product-measure equation in item 1, on supplied measures. -/
def IsUnipotentProductMeasure (dn₁ : Measure (upperUnipotent n F))
    (dn₂ : Measure (Fin n → F)) (dn : Measure (upperUnipotent (n + 1) F)) : Prop :=
  dn = unipotentProductMeasure dn₁ dn₂

variable [TopologicalSpace F] [IsTopologicalRing F]
  [BorelSpace (upperUnipotent n F × (Fin n → F))]
  [BorelSpace (upperUnipotent (n + 1) F)]

/-- Transport back recovers the whole product measure, without taking marginals. -/
theorem map_unipotentProductCoordinates (dn₁ : Measure (upperUnipotent n F))
    (dn₂ : Measure (Fin n → F)) :
    Measure.map unipotentProductCoordinates (unipotentProductMeasure dn₁ dn₂) =
      dn₁.prod dn₂ := by
  rw [unipotentProductMeasure, Measure.map_map
    continuous_unipotentProductCoordinates.measurable continuous_unipotentProduct.measurable]
  have he : unipotentProductCoordinates (F := F) (n := n) ∘ unipotentProduct = id := by
    funext p
    exact unipotentProductCoordinates_product p
  rw [he, Measure.map_id]

theorem unipotentProductMeasure_ne_zero_iff (dn₁ : Measure (upperUnipotent n F))
    (dn₂ : Measure (Fin n → F)) :
    unipotentProductMeasure dn₁ dn₂ ≠ 0 ↔ dn₁.prod dn₂ ≠ 0 :=
  Measure.map_ne_zero_iff continuous_unipotentProduct.measurable.aemeasurable

/-- Regularity is preserved when supplied on the product measure. -/
theorem unipotentProductMeasure_regular (dn₁ : Measure (upperUnipotent n F))
    (dn₂ : Measure (Fin n → F)) [(dn₁.prod dn₂).Regular] :
    (unipotentProductMeasure dn₁ dn₂).Regular :=
  Measure.Regular.map unipotentProductHomeomorph

theorem integrable_unipotentProductMeasure_iff (dn₁ : Measure (upperUnipotent n F))
    (dn₂ : Measure (Fin n → F)) (f : upperUnipotent (n + 1) F → ℂ) :
    Integrable f (unipotentProductMeasure dn₁ dn₂) ↔
      Integrable (fun p => f (unipotentProduct p)) (dn₁.prod dn₂) :=
  integrable_map_equiv unipotentProductHomeomorph.toMeasurableEquiv f

theorem integral_unipotentProductMeasure (dn₁ : Measure (upperUnipotent n F))
    (dn₂ : Measure (Fin n → F)) (f : upperUnipotent (n + 1) F → ℂ) :
    (∫ u, f u ∂unipotentProductMeasure dn₁ dn₂) =
      ∫ p, f (unipotentProduct p) ∂dn₁.prod dn₂ :=
  integral_map_equiv unipotentProductHomeomorph.toMeasurableEquiv f

/-- The measure equation is equivalent to recovering the specified whole product. -/
theorem isUnipotentProductMeasure_iff (dn₁ : Measure (upperUnipotent n F))
    (dn₂ : Measure (Fin n → F)) (dn : Measure (upperUnipotent (n + 1) F)) :
    IsUnipotentProductMeasure dn₁ dn₂ dn ↔
      Measure.map unipotentProductCoordinates dn = dn₁.prod dn₂ := by
  constructor
  · intro h
    rw [h, map_unipotentProductCoordinates]
  · intro h
    rw [IsUnipotentProductMeasure, unipotentProductMeasure, ← h,
      Measure.map_map continuous_unipotentProduct.measurable
        continuous_unipotentProductCoordinates.measurable]
    have he : unipotentProduct (F := F) (n := n) ∘ unipotentProductCoordinates = id := by
      funext u
      exact unipotentProduct_coordinates u
    rw [he, Measure.map_id]

end Measures
end Langlands.Shahidi
