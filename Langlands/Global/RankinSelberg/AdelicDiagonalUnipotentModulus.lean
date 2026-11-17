import Langlands.Global.RankinSelberg.EqualAnalyticModulus
import Langlands.Global.RankinSelberg.UnipotentConjugationModulus
import Langlands.GroupScheme.Rational.GeneralLinearCharacterMatrices

/-! # The unipotent conjugation modulus for arbitrary adelic diagonal points -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.AdelicDiagonalUnipotentModulus

local instance diagonalSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance diagonalSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

local instance : LocallyCompactSpace (Adeles F) := adeles_locallyCompactSpace F
local instance : SecondCountableTopology (Adeles F) := adeles_secondCountableTopology F
local instance : MeasurableSpace (Adeles F) := borel _
local instance : BorelSpace (Adeles F) := ⟨rfl⟩
local instance : MeasurableSpace (RowVector F 1) := borel _
local instance : BorelSpace (RowVector F 1) := ⟨rfl⟩

local instance : LocallyCompactSpace (RowVector F 1) :=
  inferInstanceAs (LocallyCompactSpace (Fin 1 → Fin 1 → Adeles F))
local instance : SecondCountableTopology (RowVector F 1) :=
  inferInstanceAs (SecondCountableTopology (Fin 1 → Fin 1 → Adeles F))

/-- Evaluation identifies a row with one entry with the additive adeles. -/
private def singleRowEquiv : RowVector F 1 ≃ₜ+ Adeles F where
  toFun x := x 0 0
  invFun a := fun _ _ => a
  left_inv x := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi
    subst hj
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  continuous_toFun := (continuous_apply 0).comp (continuous_apply 0)
  continuous_invFun := continuous_pi fun _ => continuous_pi fun _ => continuous_id

variable [CompactSpace (AdeleQuotient F)]

/-- The additive Haar character of multiplication by an arbitrary idele is its
actual idelic absolute value. -/
theorem addEquivAddHaarChar_mulLeft_eq_full (a : (Adeles F)ˣ) :
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft a) =
      (IdeleAbsoluteValue.full F a : ℝ≥0) := by
  let e := singleRowEquiv F
  let g : AdelicGL F 1 :=
    GroupScheme.GeneralLinear.diagonalMatrixUnits (Adeles F) (fun _ : Fin 1 => a)
  let ν : Measure (RowVector F 1) := addHaar
  let mu : Measure (Adeles F) := ν.map e
  have : IsAddHaarMeasure mu := e.isAddHaarMeasure_map ν
  have : Regular mu := Regular.map e.toHomeomorph
  have he : (ContinuousAddEquiv.mulLeft a) ∘ e = e ∘ EqualAnalytic.rightMul F 1 g := by
    funext x
    change (a : Adeles F) * x 0 0 =
      (x * (g : Matrix (Fin 1) (Fin 1) (Adeles F))) 0 0
    simp [g, Matrix.mul_apply, mul_comm]
  have hem : Measurable (e : RowVector F 1 → Adeles F) := e.continuous.measurable
  have ham : Measurable (ContinuousAddEquiv.mulLeft a : Adeles F → Adeles F) :=
    (ContinuousAddEquiv.mulLeft a).continuous.measurable
  have hgm : Measurable (EqualAnalytic.rightMul F 1 g : RowVector F 1 → RowVector F 1) :=
    (EqualAnalytic.rightMul F 1 g).continuous.measurable
  have hc : addEquivAddHaarChar (ContinuousAddEquiv.mulLeft a) =
      EqualAnalytic.rowModulus F 1 g := by
    apply HarmonicAnalysis.addEquivAddHaarChar_eq_of_smul_map mu
    change EqualAnalytic.rowModulus F 1 g •
      Measure.map (ContinuousAddEquiv.mulLeft a) (ν.map e) = ν.map e
    rw [Measure.map_map ham hem, he, ← Measure.map_map hem hgm,
      ← Measure.map_smul _ hem.aemeasurable]
    exact congrArg (Measure.map e)
      (addEquivAddHaarChar_smul_map ν (EqualAnalytic.rightMul F 1 g))
  rw [hc]
  apply NNReal.eq
  rw [EqualAnalytic.rowModulus_eq_absDet]
  unfold Langlands.Global.absDet
  have hg : AdelicGL.determinant F 1 g = a := by
    apply Units.ext
    change Matrix.det (g : Matrix (Fin 1) (Fin 1) (Adeles F)) = (a : Adeles F)
    simp [g]
  rw [hg]

open UnipotentConjugationModulus

omit [CompactSpace (AdeleQuotient F)] in
/-- The positive-root modulus character on the full adelic diagonal torus. -/
def diagonalModulus (n : ℕ) : (Fin n → (Adeles F)ˣ) →* ℝ≥0ˣ where
  toFun d := ∏ p : UpperIndex n, IdeleAbsoluteValue.full F (d p.1 * (d p.2.1)⁻¹)
  map_one' := by simp
  map_mul' d e := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    rw [← map_mul]
    congr 1
    simp only [Pi.mul_apply, mul_inv_rev]
    ac_rfl

omit [CompactSpace (AdeleQuotient F)] in
theorem diagonalModulus_coe (n : ℕ) (d : Fin n → (Adeles F)ˣ) :
    (diagonalModulus F n d : ℝ≥0) =
      ∏ p : UpperIndex n, (IdeleAbsoluteValue.full F (d p.1 * (d p.2.1)⁻¹) : ℝ≥0) := by
  simp [diagonalModulus]

omit [CompactSpace (AdeleQuotient F)] in
theorem diagonalModulus_eq_prod_Ioi (n : ℕ) (d : Fin n → (Adeles F)ˣ) :
    (diagonalModulus F n d : ℝ≥0) =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        (IdeleAbsoluteValue.full F (d i * (d j)⁻¹) : ℝ≥0) := by
  classical
  rw [diagonalModulus_coe, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (Finset.prod_subtype (Finset.Ioi i) (fun j => Finset.mem_Ioi)
    (fun j => (IdeleAbsoluteValue.full F (d i * (d j)⁻¹) : ℝ≥0))).symm

/-- An arbitrary diagonal adelic point acts on upper unitriangular Haar with
modulus equal to the product of its positive-root idelic absolute values. -/
theorem mulEquivHaarChar_conj_of_diagonal {n : ℕ}
    [MeasurableSpace (unipotentAdelic F n)] [BorelSpace (unipotentAdelic F n)]
    [LocallyCompactSpace (unipotentAdelic F n)]
    {a : Points F n} {d : Fin n → (Adeles F)ˣ}
    (ha : matrixOf a = Matrix.diagonal fun i => (d i : Adeles F))
    (hα : ∀ x, conjugation a x ∈ unipotentAdelic F n ↔ x ∈ unipotentAdelic F n) :
    mulEquivHaarChar (QuotientIntegration.subgroupAutomorphism
      (unipotentAdelic F n) (conjugation a) hα) =
        ∏ p : UpperIndex n, (IdeleAbsoluteValue.full F (d p.1 * (d p.2.1)⁻¹) : ℝ≥0) := by
  classical
  let c : UpperIndex n → (Adeles F)ˣ := fun p => d p.1 * (d p.2.1)⁻¹
  rw [mulEquivHaarChar_eq_prod_of_rankTriangular (addHaar : Measure (Adeles F))
    (fun p : UpperIndex n => n - (p.1 : ℕ)) (coordinates F n)
    (fun g k x y hxy => coordinates_mul_sub_eq g k x y hxy) _
    (fun p y => (c p : Adeles F) * y)
    (fun p => (continuous_const.mul continuous_id).measurable)
    (fun p => addEquivAddHaarChar (ContinuousAddEquiv.mulLeft (c p)))
    (fun p => addEquivAddHaarChar_smul_map _ (ContinuousAddEquiv.mulLeft (c p)))
    (fun h p => coordinates_conj_of_diagonal ha hα h p)]
  simp_rw [addEquivAddHaarChar_mulLeft_eq_full]
  rfl

/-- The product character is the Haar modulus for every diagonal adelic point. -/
theorem mulEquivHaarChar_conj_eq_diagonalModulus {n : ℕ}
    [MeasurableSpace (unipotentAdelic F n)] [BorelSpace (unipotentAdelic F n)]
    [LocallyCompactSpace (unipotentAdelic F n)]
    {a : Points F n} {d : Fin n → (Adeles F)ˣ}
    (ha : matrixOf a = Matrix.diagonal fun i => (d i : Adeles F))
    (hα : ∀ x, conjugation a x ∈ unipotentAdelic F n ↔ x ∈ unipotentAdelic F n) :
    mulEquivHaarChar (QuotientIntegration.subgroupAutomorphism
      (unipotentAdelic F n) (conjugation a) hα) = (diagonalModulus F n d : ℝ≥0) := by
  rw [diagonalModulus_coe]
  exact mulEquivHaarChar_conj_of_diagonal F ha hα

end Langlands.Global.RankinSelbergGlobal.AdelicDiagonalUnipotentModulus
