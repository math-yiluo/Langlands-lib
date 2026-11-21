import Langlands.BaseChange.CyclicSemilinearDeterminant
import Langlands.BaseChange.OrdinaryTwoBlockRadical
import Langlands.BaseChange.TwistedTwoBlockRadical
import Langlands.HarmonicAnalysis.PadicLinearHaarScaling

/-! Comparison of ordinary and twisted upper radical Haar Jacobians. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.GodementJacquet.TwoBlock Langlands.RankinSelberg Langlands.Unramified
open scoped Kronecker NNReal

universe u v w

section Algebra

variable {R : Type w} [Field R] {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local notation "B" => succBlockShape m h
local notation "I" => Fin (m 0 + 1) × Fin (m 1 + 1)

/-- In rectangular coordinates, the Levi acts by `U₀ x U₁⁻¹`. -/
private def radicalLeviMatrix : (B).Levi R →* Matrix I I R where
  toFun U := (U 0).val ⊗ₖ ((U 1)⁻¹ : GeneralLinear (m 1 + 1) R).val.transpose
  map_one' := by simp only [Pi.one_apply, inv_one, Units.val_one, Matrix.transpose_one,
    Matrix.one_kronecker_one]
  map_mul' U V := by
    simp only [Pi.mul_apply, Units.val_mul, mul_inv_rev, Matrix.transpose_mul,
      Matrix.mul_kronecker_mul]

private theorem ordinaryRadicalMatrix_eq_neg_mul (L : (B).Levi R) :
    ordinaryRadicalMatrix h L = -(radicalLeviMatrix h L⁻¹) * (1 - radicalLeviMatrix h L) := by
  have hMul : radicalLeviMatrix h L⁻¹ * radicalLeviMatrix h L = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hMat : ordinaryRadicalMatrix h L = 1 - radicalLeviMatrix h L⁻¹ := by
    simp only [ordinaryRadicalMatrix, radicalLeviMatrix, MonoidHom.coe_mk, OneHom.coe_mk, Pi.inv_apply, inv_inv]
  rw [hMat, Matrix.neg_mul, Matrix.mul_sub, Matrix.mul_one, hMul, neg_sub]

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]

private theorem radicalLeviMatrix_map_fieldAut (σ : E ≃ₐ[F] E) (D : (B).Levi E) :
    (radicalLeviMatrix h D).map σ = radicalLeviMatrix h (leviAut σ B D) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [radicalLeviMatrix, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.map_apply,
    Matrix.kronecker_apply, Matrix.transpose_apply, map_mul, leviAut_apply, ← map_inv,
    entrywiseAut_apply_apply]

private theorem radicalLeviMatrix_map_baseChange (L : (B).Levi F) :
    (radicalLeviMatrix h L).map (algebraMap F E) =
      radicalLeviMatrix h (fun i => baseChange F E ((B).size i) (L i)) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [radicalLeviMatrix, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.map_apply,
    Matrix.kronecker_apply, Matrix.transpose_apply, map_mul, ← map_inv, baseChange_apply_apply]

private def radicalSemilinearDefect (σ : E ≃ₐ[F] E) (D : (B).Levi E) : Module.End F (I → E) :=
  1 - (Matrix.toLinAlgEquiv' (radicalLeviMatrix h D)).restrictScalars F * coordinateFieldAut σ I

private theorem det_radicalSemilinearDefect {σ : E ≃ₐ[F] E} {l : ℕ} (hσ : IsCyclicAlgebra σ l)
    (L : (B).Levi F) (D : (B).Levi E)
    (hn : ∀ i : Fin 2, cyclicNorm σ l (D i) = baseChange F E (m i + 1) (L i)) :
    (radicalSemilinearDefect h σ D).det = (1 - radicalLeviMatrix h L).det := by
  let : Module.Finite F E := hσ.1
  let : FiniteDimensional F (I → E) := FiniteDimensional.trans F E (I → E)
  let L' : (B).Levi E := fun i => baseChange F E ((B).size i) (L i)
  have hList : ((List.range l).map fun i => leviAut (σ ^ i) B D).prod = L' := by
    funext i
    rw [show (((List.range l).map fun j => leviAut (σ ^ j) B D).prod) i =
        ((List.range l).map fun j => entrywiseAut (σ ^ j) ((B).size i) (D i)).prod from by
      have hh := map_list_prod (Pi.evalMonoidHom (fun j => GeneralLinear ((B).size j) E) i)
        ((List.range l).map fun j => leviAut (σ ^ j) B D)
      rw [List.map_map] at hh
      exact hh]
    exact hn i
  have hWeight : ((List.range l).map fun i =>
      (radicalLeviMatrix h D).map (σ ^ i : E ≃ₐ[F] E)).prod = radicalLeviMatrix h L' := by
    calc
      _ = (((List.range l).map fun i => leviAut (σ ^ i) B D).map (radicalLeviMatrix h)).prod := by
        simp only [List.map_map, radicalLeviMatrix_map_fieldAut]
        rfl
      _ = _ := by rw [← map_list_prod, hList]
  have hMap : (1 - radicalLeviMatrix h L).map (algebraMap F E) = 1 - radicalLeviMatrix h L' := by
    rw [← radicalLeviMatrix_map_baseChange h L]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.one_apply]
    split <;> simp
  apply (algebraMap F E).injective
  change algebraMap F E (radicalSemilinearDefect h σ D).det = _
  rw [radicalSemilinearDefect, hσ.det_cyclicSemilinearDefect, hWeight, RingHom.map_det]
  change (1 - radicalLeviMatrix h L').det = ((1 - radicalLeviMatrix h L).map (algebraMap F E)).det
  rw [hMap]

end Algebra

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

local instance jacobianFieldT2 {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p) : T2Space K.Carrier :=
  K.canonicalTopologicalData.fieldT2
local instance jacobianFieldMeasurable {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p) :
    MeasurableSpace K.Carrier := borel _
local instance jacobianFieldBorel {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p) :
    BorelSpace K.Carrier := ⟨rfl⟩
local instance jacobianFieldSecondCountable {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p) :
    SecondCountableTopology K.Carrier := K.canonicalTopologicalData.secondCountableTopology

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [IsModuleTopology F.Carrier E.Carrier]
    {σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier} {l t : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i + 1) = t + 1)

local notation "B" => succBlockShape m h
local notation "I" => Fin (m 0 + 1) × Fin (m 1 + 1)
local notation "Rect" => Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) E.Carrier

set_option maxHeartbeats 3000000 in
/-- At blockwise exact cyclic norms, the twisted radical pushforward has the
same inverse absolute Jacobian as the ordinary radical pushforward. -/
theorem map_twistedRadicalDifference_of_exactNorm (hσ : IsCyclicAlgebra σ l)
    (L : (B).Levi F.Carrier) (D : (B).Levi E.Carrier)
    (hn : ∀ i : Fin 2, cyclicNorm σ l (D i) = baseChange F.Carrier E.Carrier (m i + 1) (L i))
    (hCop : Pairwise fun i j => IsCoprime (L i).val.charpoly (L j).val.charpoly)
    (dx : Measure Rect) [dx.IsAddHaarMeasure] :
    Measure.map (twistedRadicalDifference σ h D) dx =
      (F.canonicalTopologicalData.normalizedAbsHom (ordinaryRadicalMatrix h L).det)⁻¹ • dx := by
  let TF := F.canonicalTopologicalData
  let TE := E.canonicalTopologicalData
  let : FiniteDimensional F.Carrier E.Carrier := hσ.1
  let : FiniteDimensional E.Carrier Rect := inferInstanceAs
    (FiniteDimensional E.Carrier (Fin (m 0 + 1) → Fin (m 1 + 1) → E.Carrier))
  let : FiniteDimensional F.Carrier Rect := FiniteDimensional.trans F.Carrier E.Carrier Rect
  let : IsModuleTopology F.Carrier Rect := inferInstanceAs
    (IsModuleTopology F.Carrier (Fin (m 0 + 1) → Fin (m 1 + 1) → E.Carrier))
  let e : Rect ≃ₗ[F.Carrier] (I → E.Carrier) :=
    { toEquiv := (Equiv.curry _ _ _).symm, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let P : Module.End F.Carrier Rect := e.symm.toLinearMap.comp
    ((radicalSemilinearDefect h σ D).comp e.toLinearMap)
  let Q (x : Rect) : Rect := ((D 0)⁻¹ : GeneralLinear (m 0 + 1) E.Carrier).val * x * (D 1).val
  let s : ℝ≥0 := (TE.determinantNorm (m 0 + 1) (D 0)⁻¹ : ℝ≥0) ^ (m 1 + 1) /
    (TE.determinantNorm (m 1 + 1) (D 1)⁻¹ : ℝ≥0) ^ (m 0 + 1)
  have hOrd := ordinaryRadicalMatrix_det_ne_zero F h L hCop
  have hDetOrd : (ordinaryRadicalMatrix h L).det =
      (-(radicalLeviMatrix h L⁻¹)).det * (1 - radicalLeviMatrix h L).det := by
    rw [ordinaryRadicalMatrix_eq_neg_mul, Matrix.det_mul]
  have hDetZero : (1 - radicalLeviMatrix h L).det ≠ 0 := by
    intro hz
    apply hOrd
    rw [hDetOrd, hz, mul_zero]
  have hDetP : P.det = (1 - radicalLeviMatrix h L).det := by
    calc
      _ = (radicalSemilinearDefect h σ D).det := LinearMap.det_conj _ e.symm
      _ = _ := det_radicalSemilinearDefect h hσ L D hn
  have hMapP : Measure.map P dx = (TF.normalizedAbsHom (1 - radicalLeviMatrix h L).det)⁻¹ • dx := by
    rw [padicLinearHaarScaling F dx P (hDetP.symm ▸ hDetZero), hDetP]
  have hMapQ : Measure.map Q dx = s⁻¹ • dx := by
    simpa only [Q, s, inv_inv] using
      padicRectangularHaarScaling E TE (m 0 + 1) (m 1 + 1) dx (D 0)⁻¹ (D 1)⁻¹
  have hP (x : Rect) : P x = x - (D 0).val * x.map σ * ((D 1)⁻¹ : GeneralLinear (m 1 + 1) E.Carrier).val := by
    apply e.injective
    change e (e.symm (radicalSemilinearDefect h σ D (e x))) = _
    rw [LinearEquiv.apply_symm_apply]
    unfold radicalSemilinearDefect
    have he : coordinateFieldAut σ I (e x) = e (x.map σ) := rfl
    have hm := rectangularCoordinates_mul (D 0).val
      ((D 1)⁻¹ : GeneralLinear (m 1 + 1) E.Carrier).val (x.map σ)
    change e ((D 0).val * x.map σ * ((D 1)⁻¹ : GeneralLinear (m 1 + 1) E.Carrier).val) =
      Matrix.toLin' (radicalLeviMatrix h D) (e (x.map σ)) at hm
    change e x - Matrix.toLin' (radicalLeviMatrix h D) (coordinateFieldAut σ I (e x)) = _
    rw [he, ← hm, map_sub]
  have hFactor : twistedRadicalDifference σ h D = (fun x : Rect => -x) ∘ Q ∘ P := by
    funext x
    let A := (D 0).val
    let A' := ((D 0)⁻¹ : GeneralLinear (m 0 + 1) E.Carrier).val
    let Z := (D 1).val
    let Z' := ((D 1)⁻¹ : GeneralLinear (m 1 + 1) E.Carrier).val
    have hCancel : A' * (A * x.map σ * Z') * Z = x.map σ := by
      rw [← Matrix.mul_assoc A' (A * x.map σ), ← Matrix.mul_assoc A' A]
      dsimp only [A, A', Z, Z']
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    change twistedRadicalDifference σ h D x = -Q (P x)
    rw [twistedRadicalDifference_apply, hP]
    dsimp only [Q]
    rw [Matrix.mul_sub, Matrix.sub_mul, neg_sub, hCancel]
  have hNeg : TF.normalizedAbsHom (-1 : F.Carrier) = 1 := by
    apply NNReal.eq
    rw [TF.normalizedAbsHom_coe, TF.normalizedAbs_eq_canonicalNorm_pow_degree]
    let := F.canonicalNormedField
    change ‖(-1 : F.Carrier)‖ ^ Module.finrank (Padic p) F.Carrier = 1
    simp
  have hMapNeg : Measure.map (fun x : Rect => -x) dx = dx := by
    let negLinear : Module.End F.Carrier Rect := -LinearMap.id
    have hDet : negLinear.det = (-1 : F.Carrier) ^ Module.finrank F.Carrier Rect := by
      rw [show negLinear = (-1 : F.Carrier) • LinearMap.id from (neg_one_smul _ _).symm,
        LinearMap.det_smul, LinearMap.det_id, mul_one]
    have hDet₀ : negLinear.det ≠ 0 := by
      rw [hDet]
      exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    change Measure.map (⇑negLinear) dx = dx
    rw [padicLinearHaarScaling F dx negLinear hDet₀, hDet, map_pow, hNeg, one_pow, inv_one, one_smul]
  have hBlock0 := determinantNorm_eq_of_exactNorm F E σ hσ (L 0) (D 0) (hn 0)
  have hBlock1 := determinantNorm_eq_of_exactNorm F E σ hσ (L 1) (D 1) (hn 1)
  have hAbsR : TF.normalizedAbsHom (-(radicalLeviMatrix h L⁻¹)).det = s := by
    simp only [Matrix.det_neg, map_mul, map_pow, hNeg, one_pow, one_mul,
      radicalLeviMatrix, MonoidHom.coe_mk, OneHom.coe_mk, Pi.inv_apply, inv_inv,
      Matrix.det_kronecker, Matrix.det_transpose, Fintype.card_fin]
    change (TF.determinantNorm (m 0 + 1) (L 0)⁻¹ : ℝ≥0) ^ (m 1 + 1) *
      (TF.determinantNorm (m 1 + 1) (L 1) : ℝ≥0) ^ (m 0 + 1) = s
    simp only [s, TE, TF, map_inv, hBlock0, hBlock1, Units.val_inv_eq_inv_val,
      div_eq_mul_inv, inv_pow, inv_inv]
  have hmP : Measurable (⇑P) := (IsModuleTopology.continuous_of_linearMap P).measurable
  have hmQ : Measurable Q :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  rw [hFactor, ← Measure.map_map measurable_neg (hmQ.comp hmP), ← Measure.map_map hmQ hmP,
    hMapP, Measure.map_smul _ hmQ.aemeasurable, hMapQ, Measure.map_smul _ measurable_neg.aemeasurable,
    Measure.map_smul _ measurable_neg.aemeasurable, hMapNeg,
    hDetOrd, map_mul, hAbsR, smul_smul]
  congr 1
  exact (mul_inv_rev s _).symm

end Langlands.BaseChange
