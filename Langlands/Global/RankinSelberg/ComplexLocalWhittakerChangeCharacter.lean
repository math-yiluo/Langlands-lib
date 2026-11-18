import Langlands.Automorphic.CuspidalAdmissible.CentralEigen
import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerAnalyticProof
import Langlands.Representation.Archimedean.ComplexLinkedSmallGrowthProof
import Langlands.Representation.Archimedean.ComplexPermutationSwap
import Langlands.Representation.Archimedean.ComplexTorusDerivative

/-! # Changing the generic character of the complex local Whittaker model -/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexCharacterChange

open Langlands.LocalFactor.Archimedean Langlands.Archimedean
open GeneralLinear.Iwasawa (diagonalUnits_mul_mul_apply)

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℂ

/-- The diagonal matrix with entries `a^r, a^(r-1), …, 1`. -/
def changeDiagonal (r : ℕ) (a : ℂˣ) : Langlands.GeneralLinear (r + 1) ℂ :=
  GeneralLinear.Iwasawa.diagonalUnits (F := ℂ) (fun i : Fin (r + 1) => a ^ (r - i.val))

/-- Every invertible diagonal matrix normalizes the upper unitriangular subgroup. -/
theorem diagonal_conj_mem (d : Fin (r + 1) → ℂˣ) (u : G) (hu : u ∈ N) :
    GeneralLinear.Iwasawa.diagonalUnits (F := ℂ) d * u *
      (GeneralLinear.Iwasawa.diagonalUnits (F := ℂ) d)⁻¹ ∈ N := by
  rw [← map_inv]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [diagonalUnits_mul_mul_apply, hu.1 hij, mul_zero, zero_mul]
  · rw [diagonalUnits_mul_mul_apply, hu.2 i, mul_one, Pi.inv_apply, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]

/-- Conjugation by the inverse diagonal multiplies each simple-root entry by `a⁻¹`. -/
theorem changeDiagonal_inv_conj_entry (a : ℂˣ) (u : G) (i : Fin r) :
    ((changeDiagonal r a)⁻¹ * u * changeDiagonal r a) i.castSucc i.succ =
      (a⁻¹ : ℂˣ) * u i.castSucc i.succ := by
  have hi : r - i.castSucc.val = r - i.succ.val + 1 := by
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  have hpow : ((a ^ (r - i.castSucc.val))⁻¹ * a ^ (r - i.succ.val) : ℂˣ) = a⁻¹ := by
    rw [hi, pow_succ, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  unfold changeDiagonal
  rw [← map_inv, diagonalUnits_mul_mul_apply, Pi.inv_apply]
  calc
    _ = (((a ^ (r - i.castSucc.val))⁻¹ * a ^ (r - i.succ.val) : ℂˣ) : ℂ) *
        u i.castSucc i.succ := by simp only [Units.val_mul]; ring
    _ = _ := by rw [hpow]

/-- The diagonal changes the Whittaker character for `b` to the one for `b / a`. -/
theorem changeDiagonal_character (a b : ℂˣ) (u : G) :
    complexWhittakerCharacter b ((changeDiagonal r a)⁻¹ * u * changeDiagonal r a) =
      complexWhittakerCharacter (b * a⁻¹) u := by
  unfold complexWhittakerCharacter
  simp only [changeDiagonal_inv_conj_entry, ← Finset.mul_sum]
  change ((complexScaledCharacter b
      ((a⁻¹ : ℂˣ) * ∑ i : Fin r, u i.castSucc i.succ) : Circle) : ℂ) =
      ((complexScaledCharacter (b * a⁻¹) (∑ i : Fin r, u i.castSucc i.succ) : Circle) : ℂ)
  rw [complexScaledCharacter_apply, complexScaledCharacter_apply, Units.val_mul, mul_assoc]

open scoped Matrix.Norms.Frobenius in
/-- The matrix height is submultiplicative. -/
theorem complexMatrixHeight_mul_le (x y : G) :
    complexMatrixHeight (x * y) ≤ complexMatrixHeight x * complexMatrixHeight y := by
  rw [ComplexPlaceAnalytic.complexMatrixHeight_eq_frobenius (x * y),
    ComplexPlaceAnalytic.complexMatrixHeight_eq_frobenius x,
    ComplexPlaceAnalytic.complexMatrixHeight_eq_frobenius y]
  have h₁ := Matrix.frobenius_norm_mul x.val y.val
  have h₂ := Matrix.frobenius_norm_mul (y⁻¹ : G).val (x⁻¹ : G).val
  simp only [Units.val_mul, mul_inv_rev]
  calc
    _ ≤ (‖x.val‖ * ‖y.val‖)^2 + (‖(y⁻¹ : G).val‖ * ‖(x⁻¹ : G).val‖)^2 := by
      exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h₁ 2)
        (pow_le_pow_left₀ (norm_nonneg _) h₂ 2)
    _ ≤ _ := by
      nlinarith [mul_nonneg (sq_nonneg ‖x.val‖) (sq_nonneg ‖(y⁻¹ : G).val‖),
        mul_nonneg (sq_nonneg ‖(x⁻¹ : G).val‖) (sq_nonneg ‖y.val‖)]

/-- Precomposition with left multiplication, as a linear map on functions. -/
def leftTranslate (x : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun W g := W (x * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem leftTranslate_apply (x : G) (W : G → ℂ) (g : G) :
    leftTranslate x W g = W (x * g) := rfl

/-- Left translation by the inverse diagonal takes the entire coefficient model for
`ψ_b` to the coefficient model for `ψ_(b/a)`. -/
theorem leftTranslate_mem_model {ds : List ComplexCharacterData} (a b : ℂˣ)
    {W : G → ℂ} (hW : W ∈ complexWhittakerModel r ds b) :
    leftTranslate (changeDiagonal r a)⁻¹ W ∈ complexWhittakerModel r ds (b * a⁻¹) := by
  let t := changeDiagonal r a
  let L := leftTranslate t⁻¹
  change L W ∈ complexWhittakerModel r ds (b * a⁻¹)
  have hle : complexWhittakerModel r ds b ≤ (complexWhittakerModel r ds (b * a⁻¹)).comap L := by
    refine iSup₂_le fun B hB => ?_
    rintro _ ⟨f, rfl⟩
    let B' := L.comp B
    have hB' : IsComplexWhittakerIntertwiner r ds (b * a⁻¹) B' := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro f u hu g
        change B f (t⁻¹ * (u * g)) = complexWhittakerCharacter (b * a⁻¹) u * B f (t⁻¹ * g)
        have hN : t⁻¹ * u * t ∈ N := by
          have h := diagonal_conj_mem ((fun i : Fin (r + 1) => a ^ (r - i.val))⁻¹) u hu
          rw [map_inv, inv_inv] at h
          exact h
        have hprod : t⁻¹ * (u * g) = (t⁻¹ * u * t) * (t⁻¹ * g) := by group
        rw [hprod, hB.1 _ _ hN, changeDiagonal_character]
      · intro f
        exact (hB.2.1 f).comp contMDiff_mul_left
      · intro f
        obtain ⟨C, k, hk⟩ := hB.2.2.1 f
        have hnonneg (g : G) : 0 ≤ complexMatrixHeight g := by
          rw [ComplexPlaceAnalytic.complexMatrixHeight_eq_frobenius]
          positivity
        refine ⟨max C 0 * complexMatrixHeight t⁻¹ ^ k, k, fun g => ?_⟩
        change ‖B f (t⁻¹ * g)‖ ≤ _
        calc
          _ ≤ C * complexMatrixHeight (t⁻¹ * g) ^ k := hk _
          _ ≤ max C 0 * (complexMatrixHeight t⁻¹ * complexMatrixHeight g) ^ k := by
            exact mul_le_mul (le_max_left _ _)
              (pow_le_pow_left₀ (hnonneg _) (complexMatrixHeight_mul_le _ _) _)
              (pow_nonneg (hnonneg _) _) (le_max_right _ _)
          _ = _ := by rw [mul_pow, mul_assoc]
      · intro k f f' hf
        funext g
        change B f' (t⁻¹ * g) = B f (t⁻¹ * (g * k.val))
        rw [hB.2.2.2.1 k f f' hf]
        change B f ((t⁻¹ * g) * k.val) = _
        rw [mul_assoc]
      · intro X f f' hf
        funext g
        change B f' (t⁻¹ * g) = rightDerivative (matrixModel ℂ (r + 1)) X
          (fun h => B f (t⁻¹ * h)) g
        rw [hB.2.2.2.2 X f f' hf]
        unfold rightDerivative
        have he : (fun h : G => B f (t⁻¹ * g * h)) =
            (fun h : G => B f (t⁻¹ * (g * h))) := by
          funext h
          rw [mul_assoc]
        exact congrArg (fun F : G → ℂ =>
          mfderiv (matrixModel ℂ (r + 1)) 𝓘(ℝ, ℂ) F (1 : G) X) he
    exact (le_iSup₂ (f := fun B (_ : IsComplexWhittakerIntertwiner r ds (b * a⁻¹) B) =>
      LinearMap.range B) B' hB') ⟨f, rfl⟩
  exact hle hW

/-- A pointwise linear relation on every intertwiner image holds on the model. -/
private theorem model_relation {ds : List ComplexCharacterData} {a : ℂˣ} {W : G → ℂ}
    (hW : W ∈ complexWhittakerModel r ds a) (x y : G) (c : ℂ)
    (h : ∀ (B : Automorphic.complexStandardKFinite (r + 1) ds →ₗ[ℂ] (G → ℂ)),
      IsComplexWhittakerIntertwiner r ds a B → ∀ f, B f x = c * B f y) :
    W x = c * W y := by
  let P := LinearMap.ker (LinearMap.proj x - c • LinearMap.proj y : (G → ℂ) →ₗ[ℂ] ℂ)
  have hle : complexWhittakerModel r ds a ≤ P := by
    refine iSup₂_le fun B hB => ?_
    rintro _ ⟨f, rfl⟩
    change B f x - c * B f y = 0
    rw [h B hB f, sub_self]
  exact sub_eq_zero.mp (hle hW)

/-- Whittaker equivariance holds for the span of the intertwiner images. -/
theorem model_unipotent_mul {ds : List ComplexCharacterData} {a : ℂˣ} {W : G → ℂ}
    (hW : W ∈ complexWhittakerModel r ds a) (u : N) (g : G) :
    W (u.val * g) = complexWhittakerCharacter a u.val * W g :=
  model_relation hW _ _ _ fun _ hB f => hB.1 f u u.property g

/-! ## Scalar matrices -/

/-- The central character given by the product of the inducing characters. -/
def centralCharacter (ds : List ComplexCharacterData) : ℂˣ →* ℂˣ :=
  (ds.map ComplexCharacterData.character).prod

theorem coe_centralCharacter (ds : List ComplexCharacterData) (z : ℂˣ) :
    (centralCharacter ds z : ℂ) = (ds.map fun d => (d.character z : ℂ)).prod := by
  induction ds with
  | nil => simp [centralCharacter]
  | cons d ds ih =>
    change (d.character z : ℂ) * (centralCharacter ds z : ℂ) =
      (d.character z : ℂ) * (ds.map fun d => (d.character z : ℂ)).prod
    rw [ih]

private theorem diagonalUnits_const (z : ℂˣ) :
    GeneralLinear.Iwasawa.diagonalUnits (F := ℂ) (fun _ : Fin (r + 1) => z) =
      (GeneralLinear.scalar z : G) := rfl

private theorem principalSeriesCharacter_const {ds : List ComplexCharacterData}
    (hlen : ds.length = r + 1) (z : ℂˣ) :
    principalSeriesCharacter ℂ (r + 1) (complexPositionCharacter ds) (fun _ => z) =
      (centralCharacter ds z : ℂ) := by
  let e : Fin (r + 1) → ℂ := fun i => (((r + 1 : ℕ) : ℂ) - 1) / 2 - (i.val : ℂ)
  have hrev (i : Fin (r + 1)) : e (Fin.revPerm i) = -e i := by
    have hi : (Fin.rev i).val + i.val = r := by
      rw [Fin.val_rev]
      omega
    have hic : ((Fin.rev i).val : ℂ) + (i.val : ℂ) = (r : ℂ) := by exact_mod_cast hi
    change (((r + 1 : ℕ) : ℂ) - 1) / 2 - ((Fin.rev i).val : ℂ) =
      -((((r + 1 : ℕ) : ℂ) - 1) / 2 - (i.val : ℂ))
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    linear_combination -hic
  have hsum : ∑ i, e i = 0 := by
    have h := Equiv.sum_comp Fin.revPerm e
    simp only [hrev, Finset.sum_neg_distrib] at h
    linear_combination (-1 / 2) * h
  let b : ℂ := (‖(z : ℂ)‖ ^ Module.finrank ℝ ℂ : ℝ)
  have hb : b ≠ 0 := by
    dsimp [b]
    exact_mod_cast pow_ne_zero _ (norm_ne_zero_iff.mpr z.ne_zero)
  change (∏ i : Fin (r + 1), complexPositionCharacter ds i z * b ^ e i) = _
  rw [Finset.prod_mul_distrib, LevelFunctions.prod_cpow_eq_cpow_sum _ hb, hsum, Complex.cpow_zero,
    mul_one, coe_centralCharacter]
  rw [← hlen, ← List.prod_ofFn]
  congr 1
  rw [← List.ofFn_getElem_eq_map]
  apply congrArg List.ofFn
  funext i
  rw [ComplexPermutation.complexPositionCharacter_eq_get ds i i.isLt]
  rfl

/-- Every coefficient in the model transforms by the central character on scalar matrices. -/
theorem model_mul_scalar {ds : List ComplexCharacterData} {a : ℂˣ} {W : G → ℂ}
    (hlen : ds.length = r + 1) (hW : W ∈ complexWhittakerModel r ds a) (z : ℂˣ) (g : G) :
    W (g * GeneralLinear.scalar z) = (centralCharacter ds z : ℂ) * W g := by
  refine model_relation hW _ _ _ fun B hB f => ?_
  let v : ℂ := Complex.log (z : ℂ)
  let d : Fin (r + 1) → ℂ := fun _ => v
  let X := Matrix.diagonal d
  let Λ := LevelFunctions.torusDeriv (LinkedSmallGrowth.posWeight ds)
    (LinkedSmallGrowth.posExponent ds) d
  let E (t : ℝ) : ℂˣ := Units.mk0 (Complex.exp ((t : ℂ) * v)) (Complex.exp_ne_zero _)
  let P (t : ℝ) : G := g * GeneralLinear.scalar (E t)
  have hE0 : E 0 = 1 := by
    apply Units.ext
    simp [E]
  have hE1 : E 1 = z := by
    apply Units.ext
    simp [E, v, Complex.exp_log z.ne_zero]
  have hf : (f : G → ℂ) ∈ principalSeries ℂ (r + 1) (complexPositionCharacter ds) :=
    f.property.1
  have hf_smooth := ((mem_principalSeries_iff ℂ (r + 1) _ _).mp hf).1
  have hR : ((Λ • f : Automorphic.complexStandardKFinite (r + 1) ds) : G → ℂ) =
      rightDerivative (matrixModel ℂ (r + 1)) X (f : G → ℂ) := by
    funext y
    change Λ * f.val y = _
    have hxy : X * y.val = y.val * X := Matrix.scalar_comm v (Commute.all _) y.val
    rw [rightDerivative_eq_fderiv hf_smooth,
      ← hxy, LevelFunctions.fderiv_unitsExtension_diagonal_mul _ _
        (LinkedSmallGrowth.complexPositionCharacter_eq_phase ds) hf d]
  have hB_R (y : G) : rightDerivative (matrixModel ℂ (r + 1)) X (B f) y = Λ * B f y := by
    have h := congrFun (hB.2.2.2.2 X f (Λ • f) hR) y
    rw [map_smul] at h
    exact h.symm
  have hP (t : ℝ) : (P t).val = g.val * NormedSpace.exp (t • X) := by
    change g.val * Matrix.scalar _ (E t : ℂ) = _
    rw [show X = Matrix.diagonal d from rfl, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
    simp only [E, Units.val_mk0, Pi.exp_def, Complex.exp_eq_exp_ℂ, Pi.smul_apply,
      d, Complex.real_smul]
    rfl
  have hPd (t : ℝ) : HasDerivAt (fun s => (P s).val) ((P t).val * X) t := by
    simp_rw [hP]
    simpa only [Matrix.mul_assoc] using (hasDerivAt_exp_smul_const X t).const_mul g.val
  have hBd (t : ℝ) : HasDerivAt (fun s => B f (P s)) (Λ * B f (P t)) t := by
    have h := (differentiableAt_unitsExtension (hB.2.1 f)
      (Units.isUnit (P t))).hasFDerivAt.comp_hasDerivAt t (hPd t)
    rw [← rightDerivative_eq_fderiv (hB.2.1 f), hB_R] at h
    simpa only [Function.comp_def, unitsExtension_val] using h
  have hsolution := Automorphic.OperatorRealization.eq_exp_mul_of_hasDerivAt hBd 1
  have hω : Complex.exp Λ = (centralCharacter ds z : ℂ) := by
    have h := LevelFunctions.principalSeriesCharacter_exp (LinkedSmallGrowth.posWeight ds)
      (LinkedSmallGrowth.posExponent ds) (LinkedSmallGrowth.complexPositionCharacter_eq_phase ds)
      d 1
    change principalSeriesCharacter ℂ (r + 1) (complexPositionCharacter ds) (fun _ => E 1) =
      Complex.exp ((1 : ℝ) * Λ) at h
    rw [hE1, principalSeriesCharacter_const hlen, Complex.ofReal_one, one_mul] at h
    exact h.symm
  simpa only [P, hE0, hE1, map_one, mul_one, Complex.ofReal_one, hω] using hsolution

end Langlands.Global.RankinSelbergGlobal.ComplexCharacterChange
