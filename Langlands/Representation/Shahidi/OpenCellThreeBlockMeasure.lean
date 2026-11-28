import Langlands.Representation.Shahidi.OpenCellThreeBlockCoordinates

/-! # The change of variables between the two three-block coordinate systems

The map `(Y, z) ↦ (Y_a, [Y_b - Y_a z; z])`, from
`M_((t+1)×(1+(d+1)))(K) × M_((d+1)×1)(K)` to `M_((t+1)×(d+1))(K) × M_(((d+1)+(t+1))×1)(K)`,
where `Y = [Y_a | Y_b]` with `Y_b` the last column, preserves the product Haar measures. It is
the composite of coordinate regroupings and the shear `Y_b ↦ Y_b - Y_a z`, which is a
translation for fixed `(Y_a, z)`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open MeasureTheory
open scoped ENNReal NNReal

universe u

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance ocTBMTopologicalSpace : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance ocTBMValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocTBMLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance ocTBMT2Space : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocTBMSecondCountableTopology : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocTBMMeasurableSpace : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocTBMBorelSpace : BorelSpace K.Carrier := ⟨rfl⟩

variable (d t : ℕ)

/-- The columns of `1 + (d+1)` split as the first `d + 1` and the last one. -/
def columnEquiv : Fin (d + 1) ⊕ Fin (0 + 1) ≃ Fin ((0 + 1) + (d + 1)) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm (d + 1) (0 + 1)))

/-- The rows of `(d+1) + (t+1)` split as the first `t + 1` and the last `d + 1`. -/
def rowEquiv : Fin (t + 1) ⊕ Fin (d + 1) ≃ Fin ((d + 1) + (t + 1)) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm (t + 1) (d + 1)))

@[simp] theorem columnEquiv_inl_val (b : Fin (d + 1)) : (columnEquiv d (Sum.inl b)).val = b.val := rfl

@[simp] theorem columnEquiv_inr_val (j : Fin (0 + 1)) :
    (columnEquiv d (Sum.inr j)).val = d + 1 + j.val := rfl

@[simp] theorem rowEquiv_inl_val (i : Fin (t + 1)) : (rowEquiv d t (Sum.inl i)).val = i.val := rfl

@[simp] theorem rowEquiv_inr_val (j : Fin (d + 1)) :
    (rowEquiv d t (Sum.inr j)).val = t + 1 + j.val := rfl

/-- Splitting off the last column. -/
def columnSplitEquiv : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) K.Carrier ≃ᵐ
    Matrix (Fin (t + 1)) (Fin (d + 1)) K.Carrier × Matrix (Fin (t + 1)) (Fin (0 + 1)) K.Carrier :=
  (MeasurableEquiv.piCongrRight fun _ : Fin (t + 1) =>
    (MeasurableEquiv.piCongrLeft (fun _ => K.Carrier) (columnEquiv d)).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (d + 1) ⊕ Fin (0 + 1) => K.Carrier))).trans
  (MeasurableEquiv.arrowProdEquivProdArrow _ _ _)

theorem columnSplitEquiv_apply (Y : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) K.Carrier) :
    columnSplitEquiv K d t Y =
      (fun i b => Y i (columnEquiv d (Sum.inl b)), fun i j => Y i (columnEquiv d (Sum.inr j))) := by
  rfl

/-- Splitting the rows of a column. -/
def rowSplitEquiv : Matrix (Fin ((d + 1) + (t + 1))) (Fin (0 + 1)) K.Carrier ≃ᵐ
    Matrix (Fin (t + 1)) (Fin (0 + 1)) K.Carrier × Matrix (Fin (d + 1)) (Fin (0 + 1)) K.Carrier :=
  (MeasurableEquiv.piCongrLeft (fun _ => Fin (0 + 1) → K.Carrier) (rowEquiv d t)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (t + 1) ⊕ Fin (d + 1) => Fin (0 + 1) → K.Carrier))

theorem rowSplitEquiv_apply (y : Matrix (Fin ((d + 1) + (t + 1))) (Fin (0 + 1)) K.Carrier) :
    rowSplitEquiv K d t y = (fun i => y (rowEquiv d t (Sum.inl i)), fun j => y (rowEquiv d t (Sum.inr j))) := by
  rfl

theorem measurePreserving_columnSplitEquiv :
    MeasurePreserving (columnSplitEquiv K d t) (matrixHaar K (t + 1) ((0 + 1) + (d + 1)))
      ((matrixHaar K (t + 1) (d + 1)).prod (matrixHaar K (t + 1) (0 + 1))) := by
  have hrow := (measurePreserving_sumPiEquivProdPi
      (fun _ : Fin (d + 1) ⊕ Fin (0 + 1) => (haarK K).measure)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin ((0 + 1) + (d + 1)) => (haarK K).measure)
      (columnEquiv d)).symm
  have hpi := measurePreserving_pi (fun _ : Fin (t + 1) => Measure.pi fun _ => (haarK K).measure)
    (fun _ : Fin (t + 1) => (Measure.pi fun _ : Fin (d + 1) => (haarK K).measure).prod
      (Measure.pi fun _ : Fin (0 + 1) => (haarK K).measure)) (fun _ => hrow)
  have harr := measurePreserving_arrowProdEquivProdArrow (Fin (d + 1) → K.Carrier)
    (Fin (0 + 1) → K.Carrier) (Fin (t + 1)) (fun _ => Measure.pi fun _ => (haarK K).measure)
    (fun _ => Measure.pi fun _ => (haarK K).measure)
  exact harr.comp hpi

theorem measurePreserving_rowSplitEquiv :
    MeasurePreserving (rowSplitEquiv K d t) (matrixHaar K ((d + 1) + (t + 1)) (0 + 1))
      ((matrixHaar K (t + 1) (0 + 1)).prod (matrixHaar K (d + 1) (0 + 1))) :=
  (measurePreserving_sumPiEquivProdPi
      (fun _ : Fin (t + 1) ⊕ Fin (d + 1) => Measure.pi fun _ : Fin (0 + 1) => (haarK K).measure)).comp
    (measurePreserving_piCongrLeft
      (fun _ : Fin ((d + 1) + (t + 1)) => Measure.pi fun _ : Fin (0 + 1) => (haarK K).measure)
      (rowEquiv d t)).symm

theorem measurable_matrix_mul {α : Type*} [MeasurableSpace α] {a b c : ℕ}
    {f : α → Matrix (Fin a) (Fin b) K.Carrier} {g : α → Matrix (Fin b) (Fin c) K.Carrier}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x * g x := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hf.eval_matrix).mul (hg.eval_matrix)

/-- The shear `((Y_a, z), Y_b) ↦ ((Y_a, z), Y_b - Y_a z)`. -/
def shearEquiv : (Matrix (Fin (t + 1)) (Fin (d + 1)) K.Carrier × Matrix (Fin (d + 1)) (Fin (0 + 1)) K.Carrier) ×
      Matrix (Fin (t + 1)) (Fin (0 + 1)) K.Carrier ≃ᵐ
    (Matrix (Fin (t + 1)) (Fin (d + 1)) K.Carrier × Matrix (Fin (d + 1)) (Fin (0 + 1)) K.Carrier) ×
      Matrix (Fin (t + 1)) (Fin (0 + 1)) K.Carrier where
  toFun x := (x.1, x.2 - x.1.1 * x.1.2)
  invFun x := (x.1, x.2 + x.1.1 * x.1.2)
  left_inv x := by simp
  right_inv x := by simp
  measurable_toFun := by
    refine measurable_fst.prodMk (Measurable.of_eval_matrix _ fun i j => ?_)
    simp only [Matrix.sub_apply]
    exact (measurable_snd.eval_matrix).sub
      ((measurable_matrix_mul K measurable_fst.fst measurable_fst.snd).eval_matrix)
  measurable_invFun := by
    refine measurable_fst.prodMk (Measurable.of_eval_matrix _ fun i j => ?_)
    simp only [Matrix.add_apply]
    exact (measurable_snd.eval_matrix).add
      ((measurable_matrix_mul K measurable_fst.fst measurable_fst.snd).eval_matrix)

theorem measurePreserving_shearEquiv :
    MeasurePreserving (shearEquiv K d t)
      (((matrixHaar K (t + 1) (d + 1)).prod (matrixHaar K (d + 1) (0 + 1))).prod
        (matrixHaar K (t + 1) (0 + 1)))
      (((matrixHaar K (t + 1) (d + 1)).prod (matrixHaar K (d + 1) (0 + 1))).prod
        (matrixHaar K (t + 1) (0 + 1))) := by
  have hgm : Measurable (Function.uncurry fun (a : Matrix (Fin (t + 1)) (Fin (d + 1)) K.Carrier ×
      Matrix (Fin (d + 1)) (Fin (0 + 1)) K.Carrier) (v : Matrix (Fin (t + 1)) (Fin (0 + 1)) K.Carrier) =>
        v - a.1 * a.2) :=
    (shearEquiv K d t).measurable_toFun.snd
  exact (MeasurePreserving.id _).skew_product hgm
    (Filter.Eventually.of_forall fun a => (measurePreserving_sub_right _ (a.1 * a.2)).map_eq)

/-- The change of variables `(Y, z) ↦ (Y_a, [Y_b - Y_a z; z])`. -/
def threeBlockChange : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) K.Carrier ×
      Matrix (Fin (d + 1)) (Fin (0 + 1)) K.Carrier ≃ᵐ
    Matrix (Fin (t + 1)) (Fin (d + 1)) K.Carrier × Matrix (Fin ((d + 1) + (t + 1))) (Fin (0 + 1)) K.Carrier :=
  (((((columnSplitEquiv K d t).prodCongr (MeasurableEquiv.refl _)).trans
    ((MeasurableEquiv.prodAssoc.trans
      ((MeasurableEquiv.refl _).prodCongr MeasurableEquiv.prodComm)).trans
      MeasurableEquiv.prodAssoc.symm)).trans (shearEquiv K d t)).trans
    (MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl _).prodCongr MeasurableEquiv.prodComm))).trans
    ((MeasurableEquiv.refl _).prodCongr (rowSplitEquiv K d t).symm)

theorem measurePreserving_threeBlockChange :
    MeasurePreserving (threeBlockChange K d t)
      ((matrixHaar K (t + 1) ((0 + 1) + (d + 1))).prod (matrixHaar K (d + 1) (0 + 1)))
      ((matrixHaar K (t + 1) (d + 1)).prod (matrixHaar K ((d + 1) + (t + 1)) (0 + 1))) := by
  have h1 := (measurePreserving_columnSplitEquiv K d t).prod
    (MeasurePreserving.id (matrixHaar K (d + 1) (0 + 1)))
  have h2 := ((measurePreserving_prodAssoc (matrixHaar K (t + 1) (d + 1))
      (matrixHaar K (d + 1) (0 + 1)) (matrixHaar K (t + 1) (0 + 1))).symm).comp
    (((MeasurePreserving.id (matrixHaar K (t + 1) (d + 1))).prod
      (Measure.measurePreserving_swap (μ := matrixHaar K (t + 1) (0 + 1))
        (ν := matrixHaar K (d + 1) (0 + 1)))).comp
      (measurePreserving_prodAssoc (matrixHaar K (t + 1) (d + 1)) (matrixHaar K (t + 1) (0 + 1))
        (matrixHaar K (d + 1) (0 + 1))))
  have h4 := ((MeasurePreserving.id (matrixHaar K (t + 1) (d + 1))).prod
      (Measure.measurePreserving_swap (μ := matrixHaar K (d + 1) (0 + 1))
        (ν := matrixHaar K (t + 1) (0 + 1)))).comp
    (measurePreserving_prodAssoc (matrixHaar K (t + 1) (d + 1)) (matrixHaar K (d + 1) (0 + 1))
      (matrixHaar K (t + 1) (0 + 1)))
  have h5 := (MeasurePreserving.id (matrixHaar K (t + 1) (d + 1))).prod
    (measurePreserving_rowSplitEquiv K d t).symm
  exact h5.comp (h4.comp ((measurePreserving_shearEquiv K d t).comp (h2.comp h1)))

theorem threeBlockChange_apply (Y : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) K.Carrier)
    (z : Matrix (Fin (d + 1)) (Fin (0 + 1)) K.Carrier) :
    threeBlockChange K d t (Y, z) = (headColumns d t Y, shearColumn d t Y z) := by
  refine Prod.ext rfl ?_
  change (rowSplitEquiv K d t).symm _ = _
  rw [MeasurableEquiv.symm_apply_eq, rowSplitEquiv_apply]
  refine Prod.ext ?_ ?_
  · funext i j
    have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
    subst hj
    have hi : (rowEquiv d t (Sum.inl i)).val < t + 1 := by simp only [rowEquiv_inl_val]; omega
    simp only [shearColumn, hi, dite_true]
    change Y i (columnEquiv d (Sum.inr 0)) - ∑ b, Y i (columnEquiv d (Sum.inl b)) * z b 0 = _
    congr 1
  · funext k j
    have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
    subst hj
    have hk : ¬ (rowEquiv d t (Sum.inr k)).val < t + 1 := by simp only [rowEquiv_inr_val]; omega
    simp only [shearColumn, hk, dite_false]
    change z k 0 = _
    exact congrArg (fun b => z b 0) (Fin.ext (by simp))

end Langlands.Shahidi.OpenCell
