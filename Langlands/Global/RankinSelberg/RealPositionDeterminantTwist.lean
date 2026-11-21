import Langlands.Global.RankinSelberg.RealMatrixHeightBounds
import Langlands.LocalFactor.ArchimedeanPairFactor
import Langlands.Representation.Archimedean.RealBlockPositionData
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.Group.GL.Maps

/-! # Real determinant twists on positions of a smooth principal series -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries

open RealJacquetFrobenius RealBlockPosition RealPlaceRestriction

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- The scalar real character of the actual group determinant. -/
def realDetCharacter (c : RealCharacterData) (g : G) : ℂ := (c.character (determinant g) : ℂ)

theorem realDetCharacter_apply (c : RealCharacterData) (g : G) :
    realDetCharacter c g = charFun c.parity c.exponent g.val.det := c.character_eq _

theorem realDetCharacter_mul (c : RealCharacterData) (g h : G) :
    realDetCharacter c (g * h) = realDetCharacter c g * realDetCharacter c h := by
  simp only [realDetCharacter, map_mul, Units.val_mul]

theorem realDetCharacter_ne_zero (c : RealCharacterData) (g : G) : realDetCharacter c g ≠ 0 :=
  Units.ne_zero _

/-- The determinant character of the inverse transpose is the reciprocal character. -/
theorem realDetCharacter_inverseTranspose (c : RealCharacterData) (g : G) :
    realDetCharacter c (inverseTranspose n ℝ g) = (realDetCharacter c g)⁻¹ := by
  have hd : determinant (inverseTranspose n ℝ g) = (determinant g)⁻¹ := by
    apply Units.ext
    change (inverseTranspose n ℝ g).val.det = (((determinant g)⁻¹ : ℝˣ) : ℝ)
    rw [inverseTranspose_coe, Matrix.det_transpose]
    exact congrArg Units.val (map_inv determinant g)
  rw [realDetCharacter, hd, map_inv, Units.val_inv_eq_inv_val]
  rfl

/-- The determinant character is smooth on the real general linear group. -/
theorem contMDiff_realDetCharacter (c : RealCharacterData) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (realDetCharacter (n := n) c) := by
  refine contMDiff_of_contDiffOn (ψ := fun X : Mat => charFun c.parity c.exponent X.det) ?_ (realDetCharacter_apply c)
  intro X hX
  have hd : X.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det X).mp hX).ne_zero
  exact ((contDiffAt_charFun c.parity c.exponent hd).comp X
    (RealPrincipalSeriesDuality.contDiff_det (n := n) ∞).contDiffAt).contDiffWithinAt

theorem norm_realDetCharacter (c : RealCharacterData) (g : G) :
    ‖realDetCharacter c g‖ = |g.val.det| ^ c.exponent.re := by
  have hd : 0 < |g.val.det| := abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)
  rw [realDetCharacter_apply, charFun, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_abs, div_self hd.ne', one_pow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hd]

/-- Any fixed real determinant character has polynomial growth in the matrix/inverse height. -/
theorem exists_realDetCharacter_height (hn : 0 < n) (c : RealCharacterData) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g : G, ‖realDetCharacter c g‖ ≤ C * realMatrixHeight g ^ N := by
  simpa only [norm_realDetCharacter] using exists_det_rpow_le_realMatrixHeight hn c.exponent.re

private theorem determinant_realDiagonalUnits (a : Fin n → ℝˣ) :
    determinant (Iwasawa.diagonalUnits a : G) = ∏ i, a i := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Iwasawa.diagonalUnits_val,
    Matrix.det_diagonal, Units.coe_prod]

private theorem realDetCharacter_upperUnipotent (c : RealCharacterData) (u : upperUnipotent n ℝ) :
    realDetCharacter c u.val = 1 := by
  have hd : determinant (u : G) = 1 := by
    apply Units.ext
    exact MaximalParabolicIntegration.det_upperUnipotent u
  simp only [realDetCharacter, hd, map_one, Units.val_one]

theorem realDetCharacter_diagonal (c : RealCharacterData) (a : Fin n → ℝˣ) :
    realDetCharacter c (Iwasawa.diagonalUnits a : G) = ∏ i, (c.character (a i) : ℂ) := by
  rw [realDetCharacter, determinant_realDiagonalUnits, map_prod, Units.coe_prod]

/-- Multiplying by the determinant character multiplies each inducing character by `c`. -/
theorem realDetCharacter_mul_mem_principalSeries (c : RealCharacterData) {χ χ' : ℕ → ℝˣ → ℂ}
    (hχ : ∀ (i : Fin n) (x : ℝˣ), χ' i x = χ i x * (c.character x : ℂ))
    {f : G → ℂ} (hf : f ∈ principalSeries ℝ n χ) :
    (fun g => realDetCharacter c g * f g) ∈ principalSeries ℝ n χ' := by
  refine ⟨RealPrincipalSeriesDuality.contMDiff_mul_fun (contMDiff_realDetCharacter c) hf.1,
    fun a u g => ?_⟩
  have he : principalSeriesCharacter ℝ n χ' a =
      principalSeriesCharacter ℝ n χ a * ∏ i, (c.character (a i) : ℂ) := by
    unfold principalSeriesCharacter
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hχ]
    ring
  change realDetCharacter c (_ * _ * g) * f (_ * _ * g) =
    principalSeriesCharacter ℝ n χ' a * (realDetCharacter c g * f g)
  rw [realDetCharacter_mul, realDetCharacter_mul, realDetCharacter_diagonal, realDetCharacter_upperUnipotent,
    hf.2 a u g, he]
  ring

/-- The real character data of the first `n` positions, each twisted by `c`. -/
def twistedPositionCharacterData (ds : List RealBlock) (c : RealCharacterData) (i : Fin n) : RealCharacterData :=
  (charData (realPositionSign ds i) (GramFormula.realPositionExponent ds i)).mul c

/-- The character-block list of the twisted real position characters. -/
def twistedPositionList (n : ℕ) (ds : List RealBlock) (c : RealCharacterData) : List RealBlock :=
  (List.ofFn (twistedPositionCharacterData (n := n) ds c)).map RealBlock.character

theorem realPositionCharacter_twistedPositionList (ds : List RealBlock) (c : RealCharacterData)
    (i : Fin n) (x : ℝˣ) :
    realPositionCharacter (twistedPositionList n ds c) i x = realPositionCharacter ds i x * (c.character x : ℂ) := by
  unfold twistedPositionList
  rw [realPositionCharacter_map_character _ i (by simp), List.getElem_ofFn,
    realPositionCharacter_eq_charFun]
  rfl

private theorem positionSign_character_list :
    ∀ (ds : List RealCharacterData) (i : ℕ) (hi : i < ds.length),
      realPositionSign (ds.map RealBlock.character) i = ds[i].parity
  | [], _, hi => by simp at hi
  | d :: ds, 0, _ => rfl
  | _ :: ds, i + 1, hi => positionSign_character_list ds i (by simpa using hi)

private theorem positionExponent_character_list :
    ∀ (ds : List RealCharacterData) (i : ℕ) (hi : i < ds.length),
      GramFormula.realPositionExponent (ds.map RealBlock.character) i = ds[i].exponent
  | [], _, hi => by simp at hi
  | d :: ds, 0, _ => rfl
  | _ :: ds, i + 1, hi => positionExponent_character_list ds i (by simpa using hi)

theorem realPositionSign_twistedPositionList (ds : List RealBlock) (c : RealCharacterData) (i : Fin n) :
    realPositionSign (twistedPositionList n ds c) i = realPositionSign ds i + c.parity := by
  unfold twistedPositionList
  rw [positionSign_character_list _ i (by simp), List.getElem_ofFn]
  rfl

theorem realPositionExponent_twistedPositionList (ds : List RealBlock) (c : RealCharacterData) (i : Fin n) :
    GramFormula.realPositionExponent (twistedPositionList n ds c) i = GramFormula.realPositionExponent ds i + c.exponent := by
  unfold twistedPositionList
  rw [positionExponent_character_list _ i (by simp), List.getElem_ofFn]
  rfl

/-- The actual determinant twist lands in the smooth principal series of the twisted position
list, whose characters are multiplied, parities added mod two and exponents added. -/
def RealPositionDeterminantTwistStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock) (c : RealCharacterData),
    (∀ (i : Fin n) (x : ℝˣ), realPositionCharacter (twistedPositionList n ds c) i x =
      realPositionCharacter ds i x * (c.character x : ℂ)) ∧
    (∀ i : Fin n, realPositionSign (twistedPositionList n ds c) i = realPositionSign ds i + c.parity ∧
      GramFormula.realPositionExponent (twistedPositionList n ds c) i = GramFormula.realPositionExponent ds i + c.exponent) ∧
    ∀ (f : Langlands.GeneralLinear n ℝ → ℂ), f ∈ principalSeries ℝ n (realPositionCharacter ds) →
      (fun g => realDetCharacter c g * f g) ∈ principalSeries ℝ n (realPositionCharacter (twistedPositionList n ds c))

theorem realPositionDeterminantTwist : RealPositionDeterminantTwistStatement := by
  intro n ds c
  exact ⟨realPositionCharacter_twistedPositionList ds c,
    fun i => ⟨realPositionSign_twistedPositionList ds c i, realPositionExponent_twistedPositionList ds c i⟩,
    fun _ hf => realDetCharacter_mul_mem_principalSeries c (realPositionCharacter_twistedPositionList ds c) hf⟩

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries
