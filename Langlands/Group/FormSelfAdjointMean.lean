import Langlands.Group.AlgebraicPolar
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Algebra.MvPolynomial.Monad

/-! # Geometric means of positive forms and real self-adjointness forms -/

noncomputable section

universe u

namespace Langlands.Group.FormSelfAdjointMean

open Matrix
open Langlands.GroupScheme.GeneralLinear
open Langlands.Group.AlgebraicMatrixPowers
open Langlands.Group.AlgebraicPolar
open scoped ComplexOrder

variable {𝕜 : Type u} [RCLike 𝕜] {n : Type} [Fintype n] [DecidableEq n]

/-- A subgroup is self-adjoint for the form `J` when `J⁻¹ * star g * J` stays in it. -/
def IsFormSelfAdjoint (A : Subgroup (GL n 𝕜)) (J : GL n 𝕜) : Prop :=
  ∀ g ∈ A, J⁻¹ * star g * J ∈ A

section Units

theorem star_eq_self_of_posDef {J : GL n 𝕜} (hJ : J.val.PosDef) : star J = J :=
  Units.ext (by rw [Units.coe_star]; exact hJ.isHermitian)

theorem posDef_inv {J : GL n 𝕜} (hJ : J.val.PosDef) : (J⁻¹).val.PosDef := by
  rw [Matrix.coe_units_inv]
  exact hJ.inv

theorem posDef_star_mul_self (x : GL n 𝕜) : (star x * x).val.PosDef := by
  rw [Units.val_mul, Units.coe_star, Matrix.star_eq_conjTranspose]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_iff_isUnit.mpr x.isUnit)

theorem posDef_mul_mul_of_star_eq {c J : GL n 𝕜} (hc : star c = c) (hJ : J.val.PosDef) :
    (c * J * c).val.PosDef := by
  have h := hJ.conjTranspose_mul_mul_same (B := c.val)
    (Matrix.mulVec_injective_iff_isUnit.mpr c.isUnit)
  have hc' : c.valᴴ = c.val := by
    rw [← Matrix.star_eq_conjTranspose, ← Units.coe_star, hc]
  rw [hc'] at h
  simpa only [Units.val_mul] using h

theorem positivePower_zero (g : GL n 𝕜) (hg : g.val.PosDef) : positivePower g hg 0 = 1 := by
  have h := positivePower_add g hg 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem positivePower_neg_mul (g : GL n 𝕜) (hg : g.val.PosDef) (r : ℝ) :
    positivePower g hg (-r) = (positivePower g hg r)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← positivePower_add, neg_add_cancel, positivePower_zero]

end Units

section Normalizer

/-- Coordinates of `x * a * x⁻¹` as polynomials in the coordinates of `x`. -/
def conjCoordinate (a : GL n 𝕜) : Coordinate n → MvPolynomial (Coordinate n) 𝕜
  | .entry i j => (genericMatrix n 𝕜 * (a.val.map MvPolynomial.C) * genericInverse n 𝕜 :
      Matrix n n (MvPolynomial (Coordinate n) 𝕜)) i j
  | .inverseEntry i j =>
      (genericMatrix n 𝕜 * ((a⁻¹ : GL n 𝕜).val.map MvPolynomial.C) * genericInverse n 𝕜 :
        Matrix n n (MvPolynomial (Coordinate n) 𝕜)) i j

/-- Coordinates of `x⁻¹ * a * x` as polynomials in the coordinates of `x`. -/
def invConjCoordinate (a : GL n 𝕜) : Coordinate n → MvPolynomial (Coordinate n) 𝕜
  | .entry i j => (genericInverse n 𝕜 * (a.val.map MvPolynomial.C) * genericMatrix n 𝕜 :
      Matrix n n (MvPolynomial (Coordinate n) 𝕜)) i j
  | .inverseEntry i j =>
      (genericInverse n 𝕜 * ((a⁻¹ : GL n 𝕜).val.map MvPolynomial.C) * genericMatrix n 𝕜 :
        Matrix n n (MvPolynomial (Coordinate n) 𝕜)) i j

theorem aeval_mapMatrix_map_C (x : GL n 𝕜) (b : Matrix n n 𝕜) :
    (MvPolynomial.aeval (R := 𝕜) (values x)).mapMatrix (b.map MvPolynomial.C) = b := by
  ext i j
  simp

theorem aeval_mapMatrix_genericInverse' (x : GL n 𝕜) :
    (MvPolynomial.aeval (R := 𝕜) (values x)).mapMatrix (genericInverse n 𝕜) =
      ((x⁻¹ : GL n 𝕜) : Matrix n n 𝕜) := by
  ext i j
  simp [genericInverse, values]

theorem aeval_mapMatrix_genericMatrix' (x : GL n 𝕜) :
    (MvPolynomial.aeval (R := 𝕜) (values x)).mapMatrix (genericMatrix n 𝕜) =
      (x : Matrix n n 𝕜) := by
  ext i j
  simp [genericMatrix, values]

theorem eval_conjCoordinate (a x : GL n 𝕜) (κ : Coordinate n) :
    MvPolynomial.aeval (values x) (conjCoordinate a κ) = values (x * a * x⁻¹) κ := by
  cases κ with
  | entry i j =>
    change (MvPolynomial.aeval (R := 𝕜) (values x)).mapMatrix
      (genericMatrix n 𝕜 * (a.val.map MvPolynomial.C) * genericInverse n 𝕜) i j = _
    rw [map_mul, map_mul, aeval_mapMatrix_map_C, aeval_mapMatrix_genericMatrix',
      aeval_mapMatrix_genericInverse']
    rfl
  | inverseEntry i j =>
    change (MvPolynomial.aeval (R := 𝕜) (values x)).mapMatrix
      (genericMatrix n 𝕜 * ((a⁻¹ : GL n 𝕜).val.map MvPolynomial.C) * genericInverse n 𝕜) i j = _
    rw [map_mul, map_mul, aeval_mapMatrix_map_C, aeval_mapMatrix_genericMatrix',
      aeval_mapMatrix_genericInverse']
    change _ = ((x * a * x⁻¹)⁻¹ : GL n 𝕜).val i j
    simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, Units.val_mul]

theorem eval_invConjCoordinate (a x : GL n 𝕜) (κ : Coordinate n) :
    MvPolynomial.aeval (values x) (invConjCoordinate a κ) = values (x⁻¹ * a * x) κ := by
  cases κ with
  | entry i j =>
    change (MvPolynomial.aeval (R := 𝕜) (values x)).mapMatrix
      (genericInverse n 𝕜 * (a.val.map MvPolynomial.C) * genericMatrix n 𝕜) i j = _
    rw [map_mul, map_mul, aeval_mapMatrix_map_C, aeval_mapMatrix_genericMatrix',
      aeval_mapMatrix_genericInverse']
    rfl
  | inverseEntry i j =>
    change (MvPolynomial.aeval (R := 𝕜) (values x)).mapMatrix
      (genericInverse n 𝕜 * ((a⁻¹ : GL n 𝕜).val.map MvPolynomial.C) * genericMatrix n 𝕜) i j = _
    rw [map_mul, map_mul, aeval_mapMatrix_map_C, aeval_mapMatrix_genericMatrix',
      aeval_mapMatrix_genericInverse']
    change _ = ((x⁻¹ * a * x)⁻¹ : GL n 𝕜).val i j
    simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, Units.val_mul]

theorem aeval_bind₁ (σ : Coordinate n → MvPolynomial (Coordinate n) 𝕜) (x y : GL n 𝕜)
    (hσ : ∀ κ, MvPolynomial.aeval (values x) (σ κ) = values y κ)
    (p : MvPolynomial (Coordinate n) 𝕜) :
    MvPolynomial.aeval (values x) (MvPolynomial.bind₁ σ p) =
      MvPolynomial.aeval (values y) p := by
  rw [MvPolynomial.aeval_bind₁]
  rw [show (fun κ => MvPolynomial.aeval (values x) (σ κ)) = values y from funext hσ]

/-- The normalizer of a polynomially defined subgroup is polynomially defined. -/
theorem isPolynomiallyDefined_normalizer (A : Subgroup (GL n 𝕜))
    (hA : IsPolynomiallyDefined A) : IsPolynomiallyDefined (Subgroup.normalizer (A : Set (GL n 𝕜))) := by
  obtain ⟨S, hS⟩ := hA
  refine ⟨{q | ∃ a ∈ A, ∃ p ∈ S, q = MvPolynomial.bind₁ (conjCoordinate a) p ∨
      q = MvPolynomial.bind₁ (invConjCoordinate a) p}, fun x => ?_⟩
  have hc (a : GL n 𝕜) (p : MvPolynomial (Coordinate n) 𝕜) :
      MvPolynomial.eval (values x) (MvPolynomial.bind₁ (conjCoordinate a) p) =
        MvPolynomial.eval (values (x * a * x⁻¹)) p := by
    rw [← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]
    exact aeval_bind₁ _ _ _ (eval_conjCoordinate a x) p
  have hi (a : GL n 𝕜) (p : MvPolynomial (Coordinate n) 𝕜) :
      MvPolynomial.eval (values x) (MvPolynomial.bind₁ (invConjCoordinate a) p) =
        MvPolynomial.eval (values (x⁻¹ * a * x)) p := by
    rw [← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]
    exact aeval_bind₁ _ _ _ (eval_invConjCoordinate a x) p
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · rintro hx q ⟨a, ha, p, hp, rfl | rfl⟩
    · rw [hc]
      exact (hS _).mp ((hx a).mp ha) p hp
    · rw [hi]
      have hmem : x⁻¹ * a * x ∈ A := by
        apply (hx _).mpr
        simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using ha
      exact (hS _).mp hmem p hp
  · intro hx a
    constructor
    · intro ha
      apply (hS _).mpr
      intro p hp
      rw [← hc]
      exact hx _ ⟨a, ha, p, hp, Or.inl rfl⟩
    · intro ha
      have hmem : x⁻¹ * (x * a * x⁻¹) * x ∈ A := by
        apply (hS _).mpr
        intro p hp
        rw [← hi]
        exact hx _ ⟨_, ha, p, hp, Or.inr rfl⟩
      simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using hmem

end Normalizer

section Mean

/-- If the conjugate subgroup `x * A * x⁻¹` is stable under conjugate transpose, then `A` is
self-adjoint for the positive definite form `star x * x`. -/
theorem isFormSelfAdjoint_star_mul_self {A : Subgroup (GL n 𝕜)} (x : GL n 𝕜)
    (hx : ∀ g : GL n 𝕜, x⁻¹ * g * x ∈ A → x⁻¹ * star g * x ∈ A) :
    IsFormSelfAdjoint A (star x * x) := by
  intro a ha
  have hmem := hx (x * a * x⁻¹) (by simpa only [mul_assoc, inv_mul_cancel_left,
    inv_mul_cancel, mul_one] using ha)
  simp only [star_mul, star_inv] at hmem
  convert hmem using 1
  group

/-- Two positive self-adjointness forms differ by an element of the normalizer. -/
theorem inv_mul_mem_normalizer {A : Subgroup (GL n 𝕜)} {h h' : GL n 𝕜}
    (hh : h.val.PosDef) (hh' : h'.val.PosDef)
    (hA : IsFormSelfAdjoint A h) (hA' : IsFormSelfAdjoint A h') :
    h⁻¹ * h' ∈ Subgroup.normalizer (A : Set (GL n 𝕜)) := by
  have hs : star h = h := star_eq_self_of_posDef hh
  have hs' : star h' = h' := star_eq_self_of_posDef hh'
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have hmem := hA _ (hA' a ha)
    simp only [star_mul, star_inv, star_star, hs'] at hmem
    convert hmem using 1
    group
  · intro ha
    have h1 := hA _ ha
    simp only [star_mul, star_inv, hs, hs'] at h1
    have h2 := hA' _ h1
    simp only [star_mul, star_inv, star_star, hs, hs'] at h2
    convert h2 using 1
    group

/-- Conjugating a positive power gives a conjugated diagonal power family. -/
theorem conj_positivePower (c g : GL n 𝕜) (hg : g.val.PosDef) (r : ℝ) :
    c * positivePower g hg r * c⁻¹ =
      conjugatedPower (c * Unitary.toUnits hg.isHermitian.eigenvectorUnitary)
        hg.isHermitian.eigenvalues hg.eigenvalues_pos r := by
  simp only [positivePower, conjugatedPower, MulAut.conj_apply, _root_.mul_inv_rev, mul_assoc]

/-- **Geometric mean of two forms.** If `A` is polynomially defined and self-adjoint for two
positive definite forms `h` and `h'`, then there is a positive definite `X` with
`X * h⁻¹ * X = h'` for which `A` is also self-adjoint. -/
theorem exists_mean (A : Subgroup (GL n 𝕜)) (hA : IsPolynomiallyDefined A)
    {h h' : GL n 𝕜} (hh : h.val.PosDef) (hh' : h'.val.PosDef)
    (hAh : IsFormSelfAdjoint A h) (hAh' : IsFormSelfAdjoint A h') :
    ∃ X : GL n 𝕜, X.val.PosDef ∧ X * h⁻¹ * X = h' ∧ IsFormSelfAdjoint A X := by
  set s := positivePower h hh (1 / 2) with hs_def
  have hsP : s.val.PosDef := positivePower_posDef h hh _
  have hss : s * s = h := positivePower_half_sq h hh
  have hsstar : star s = s := star_eq_self_of_posDef hsP
  have hsinv : star s⁻¹ = s⁻¹ := by rw [star_inv, hsstar]
  set q := s⁻¹ * h' * s⁻¹ with hq_def
  have hq : q.val.PosDef := posDef_mul_mul_of_star_eq hsinv hh'
  set p := positivePower q hq (1 / 2) with hp_def
  have hpP : p.val.PosDef := positivePower_posDef q hq _
  have hpp : p * p = q := positivePower_half_sq q hq
  have hN := isPolynomiallyDefined_normalizer A hA
  have key := conj_positivePower s⁻¹ q hq
  rw [inv_inv] at key
  have hz : s⁻¹ * p * s ∈ Subgroup.normalizer (A : Set (GL n 𝕜)) := by
    rw [hp_def, key]
    apply conjugatedPower_mem _ hN
    rw [← key, positivePower_one]
    have hy : s⁻¹ * q * s = h⁻¹ * h' := by
      rw [hq_def, ← hss]
      group
    rw [hy]
    exact inv_mul_mem_normalizer hh hh' hAh hAh'
  refine ⟨s * p * s, posDef_mul_mul_of_star_eq hsstar hpP, ?_, ?_⟩
  · calc s * p * s * h⁻¹ * (s * p * s) = s * (p * p) * s := by
          rw [← hss]
          group
      _ = h' := by
          rw [hpp, hq_def]
          group
  · intro g hg
    have hzinv := inv_mem hz
    rw [Subgroup.mem_normalizer_iff] at hzinv
    have hmem := (hzinv _).mp (hAh g hg)
    convert hmem using 1
    rw [← hss]
    group

open scoped MatrixOrder in
/-- **Uniqueness of the geometric mean.** A positive definite solution `X` of
`X * h⁻¹ * X = h'` is unique. -/
theorem eq_of_mul_inv_mul_eq {h h' X Y : GL n 𝕜} (hh : h.val.PosDef)
    (hX : X.val.PosDef) (hY : Y.val.PosDef)
    (hXe : X * h⁻¹ * X = h') (hYe : Y * h⁻¹ * Y = h') : X = Y := by
  set s := positivePower h hh (1 / 2)
  have hss : s * s = h := positivePower_half_sq h hh
  have hsinv : star s⁻¹ = s⁻¹ := by
    rw [star_inv, star_eq_self_of_posDef (positivePower_posDef h hh _)]
  have hWX := posDef_mul_mul_of_star_eq hsinv hX
  have hWY := posDef_mul_mul_of_star_eq hsinv hY
  have hsq : s⁻¹ * X * s⁻¹ * (s⁻¹ * X * s⁻¹) = s⁻¹ * Y * s⁻¹ * (s⁻¹ * Y * s⁻¹) := by
    have e1 : s⁻¹ * X * s⁻¹ * (s⁻¹ * X * s⁻¹) = s⁻¹ * (X * h⁻¹ * X) * s⁻¹ := by
      rw [← hss]
      group
    have e2 : s⁻¹ * Y * s⁻¹ * (s⁻¹ * Y * s⁻¹) = s⁻¹ * (Y * h⁻¹ * Y) * s⁻¹ := by
      rw [← hss]
      group
    rw [e1, e2, hXe, hYe]
  have heq : (s⁻¹ * X * s⁻¹).val = (s⁻¹ * Y * s⁻¹).val := by
    rw [← CFC.mul_self_eq_mul_self_iff _ _ hWX.posSemidef.nonneg hWY.posSemidef.nonneg,
      ← Units.val_mul, ← Units.val_mul, hsq]
  exact mul_left_cancel (mul_right_cancel (Units.ext heq))

end Mean

section Real

/-- Entrywise conjugation of matrix units. -/
def conjGL : GL n 𝕜 →* GL n 𝕜 :=
  Units.map ((starRingEnd 𝕜).mapMatrix : Matrix n n 𝕜 →+* Matrix n n 𝕜).toMonoidHom

@[simp] theorem conjGL_val (g : GL n 𝕜) :
    (conjGL g).val = g.val.map (starRingEnd 𝕜) :=
  rfl

@[simp] theorem conjGL_conjGL (g : GL n 𝕜) : conjGL (conjGL g) = g := by
  apply Units.ext
  ext i j
  simp

theorem conjGL_star (g : GL n 𝕜) : conjGL (star g) = star (conjGL g) := by
  apply Units.ext
  ext i j
  simp [Units.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

theorem posDef_conjGL {J : GL n 𝕜} (hJ : J.val.PosDef) : (conjGL J).val.PosDef := by
  have hT : (conjGL J).val = J.valᵀ := by
    ext i j
    simp only [conjGL_val, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
    exact hJ.isHermitian.apply j i
  rw [hT]
  exact Matrix.PosDef.transpose_iff.mpr hJ

/-- Entrywise conjugation of a form for a conjugation-stable subgroup is again a form. -/
theorem isFormSelfAdjoint_conjGL {A : Subgroup (GL n 𝕜)} (hc : ∀ g ∈ A, conjGL g ∈ A)
    {J : GL n 𝕜} (hform : IsFormSelfAdjoint A J) : IsFormSelfAdjoint A (conjGL J) := by
  intro g hg
  have hmem := hc _ (hform _ (hc g hg))
  rwa [map_mul, map_mul, map_inv, conjGL_star, conjGL_conjGL] at hmem

/-- **Real self-adjointness forms.** A polynomially defined subgroup that is stable under
entrywise conjugation and self-adjoint for some positive definite form is self-adjoint for a
positive definite form fixed by entrywise conjugation, namely the geometric mean of the
given form and its conjugate. -/
theorem exists_real_form (A : Subgroup (GL n 𝕜)) (hA : IsPolynomiallyDefined A)
    (hc : ∀ g ∈ A, conjGL g ∈ A) {J : GL n 𝕜} (hJ : J.val.PosDef)
    (hform : IsFormSelfAdjoint A J) :
    ∃ m : GL n 𝕜, m.val.PosDef ∧ conjGL m = m ∧ IsFormSelfAdjoint A m := by
  obtain ⟨X, hX, hXe, hXA⟩ :=
    exists_mean A hA hJ (posDef_conjGL hJ) hform (isFormSelfAdjoint_conjGL hc hform)
  refine ⟨X, hX, ?_, hXA⟩
  apply eq_of_mul_inv_mul_eq (h' := J) (posDef_conjGL hJ) (posDef_conjGL hX) hX
  · have hconj := congrArg conjGL hXe
    rwa [map_mul, map_mul, map_inv, conjGL_conjGL] at hconj
  · calc X * (conjGL J)⁻¹ * X = X * (X * J⁻¹ * X)⁻¹ * X := by rw [hXe]
      _ = J := by group

end Real

end Langlands.Group.FormSelfAdjointMean
