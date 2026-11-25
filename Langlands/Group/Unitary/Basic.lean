import Langlands.LinearAlgebra.HermitianDiagonalization
import Mathlib.Analysis.Complex.Circle
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Unitary groups of Hermitian matrices

Let `E` be a commutative `R`-algebra with an `R`-algebra endomorphism `c` (the involution of a
quadratic algebra). For a square matrix `J` over `E`,

`UnitaryGroup.ofForm c J = {g ∈ GL_ι(E) | gᵀ J c(g) = J}`

is the group of automorphisms of the sesquilinear form with Gram matrix `J`. `J` is Hermitian for
`c` when `c (J j i) = J i j` (`Matrix.IsHermitianFor`); the determinant of an element of the unitary
group of an invertible Hermitian matrix has norm one (`UnitaryGroup.det_mem_normOneSubgroup`).

`IsQuadraticInvolution c ξ`: `E` is free over `R` with basis `1, ξ`, `ξ` is invertible and
`c ξ = -ξ`. Then `c` is an involution (`IsQuadraticInvolution.involutive`), the elements fixed by
`c` come from `R` when `2` is invertible (`exists_of_fixed`), and `z c(z) = N_{E/R}(z)`
(`algebraMap_norm`). Over fields, `E / R` is a quadratic extension
(`isQuadraticExtension`), Galois when `2 ≠ 0` (`isGalois`). Hermitian matrices are congruent to
diagonal matrices with entries in `R` (`exists_eq_mul_diagonal_mul`).

The group `U(1)` of elements of norm one (`UnitaryGroup.normOneSubgroup`) is the image of
`z ↦ z / c(z)` (Hilbert's theorem 90 for a quadratic algebra:
`IsQuadraticInvolution.range_hilbert90_eq_normOneSubgroup`), and a character of `Eˣ` trivial on
`Rˣ` descends to `U(1)` (`UnitaryGroup.descendToNormOne`).
-/

open Matrix

namespace Langlands

variable {R : Type*} [CommRing R] {E : Type*} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)

/-! ### The unitary group of a form -/

/-- The unitary group of the sesquilinear form with Gram matrix `J`: the `g ∈ GL_ι(E)` with
`gᵀ J c(g) = J`. -/
def UnitaryGroup.ofForm {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι E) :
    Subgroup (GL ι E) where
  carrier := {g | (g : Matrix ι ι E)ᵀ * J * (g : Matrix ι ι E).map c = J}
  one_mem' := by simp [Matrix.map_one _ (map_zero c) (map_one c)]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.transpose_mul] at *
    rw [show ((a : Matrix ι ι E) * (b : Matrix ι ι E)).map c =
      (a : Matrix ι ι E).map c * (b : Matrix ι ι E).map c from Matrix.map_mul (f := c.toRingHom)]
    calc _ = (b : Matrix ι ι E)ᵀ * ((a : Matrix ι ι E)ᵀ * J * (a : Matrix ι ι E).map c) *
          (b : Matrix ι ι E).map c := by simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    have h1 : (a : Matrix ι ι E).map c * ((a⁻¹ : GL ι E) : Matrix ι ι E).map c = 1 := by
      rw [← show ((a : Matrix ι ι E) * ((a⁻¹ : GL ι E) : Matrix ι ι E)).map c =
        (a : Matrix ι ι E).map c * ((a⁻¹ : GL ι E) : Matrix ι ι E).map c from
          Matrix.map_mul (f := c.toRingHom), Units.mul_inv]
      exact Matrix.map_one _ (map_zero c) (map_one c)
    have h2 : ((a⁻¹ : GL ι E) : Matrix ι ι E)ᵀ * (a : Matrix ι ι E)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    calc _ = ((a⁻¹ : GL ι E) : Matrix ι ι E)ᵀ * ((a : Matrix ι ι E)ᵀ * J *
            (a : Matrix ι ι E).map c) * ((a⁻¹ : GL ι E) : Matrix ι ι E).map c := by rw [ha]
      _ = (((a⁻¹ : GL ι E) : Matrix ι ι E)ᵀ * (a : Matrix ι ι E)ᵀ) * J *
            ((a : Matrix ι ι E).map c * ((a⁻¹ : GL ι E) : Matrix ι ι E).map c) := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem UnitaryGroup.mem_ofForm_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {J : Matrix ι ι E}
    {g : GL ι E} :
    g ∈ UnitaryGroup.ofForm c J ↔ (g : Matrix ι ι E)ᵀ * J * (g : Matrix ι ι E).map c = J :=
  Iff.rfl

/-- `J` is Hermitian for `c`: `c (J j i) = J i j`. -/
def Matrix.IsHermitianFor {ι : Type*} (J : Matrix ι ι E) : Prop := ∀ i j, c (J j i) = J i j

/-! ### Quadratic involutions -/

/-- `E` is free over `R` with basis `1, ξ`, where `ξ` is invertible and `c ξ = -ξ`. -/
structure IsQuadraticInvolution (ξ : E) : Prop where
  isUnit : IsUnit ξ
  map_eq_neg : c ξ = -ξ
  exists_basis : ∃ b : Module.Basis (Fin 2) R E, b 0 = 1 ∧ b 1 = ξ

/-! ### The norm-one subgroup and Hilbert 90 -/

/-- `z ↦ z / c(z)` on `Eˣ`. -/
def UnitaryGroup.hilbert90 : Eˣ →* Eˣ := MonoidHom.id Eˣ / Units.map (c : E →* E)

/-- The elements of norm one: `z c(z) = 1`. -/
def UnitaryGroup.normOneSubgroup : Subgroup Eˣ := (MonoidHom.id Eˣ * Units.map (c : E →* E)).ker

open Classical in
/-- A character of `Eˣ` trivial on the elements fixed by `c` descends along `z ↦ z / c(z)` to its
image. -/
noncomputable def UnitaryGroup.descendToNormOne (χ : Eˣ →* Circle)
    (hχ : ∀ z : Eˣ, c z = z → χ z = 1) : (UnitaryGroup.hilbert90 c).range →* Circle :=
  (UnitaryGroup.hilbert90 c).rangeRestrict.liftOfSurjective
    (UnitaryGroup.hilbert90 c).rangeRestrict_surjective ⟨χ, fun z hz => hχ z (by
      rw [MonoidHom.ker_rangeRestrict] at hz
      exact (congrArg Units.val (div_eq_one.mp hz)).symm)⟩

namespace UnitaryGroup

variable {c}

theorem mem_normOneSubgroup {u : Eˣ} : u ∈ normOneSubgroup c ↔ (u : E) * c u = 1 :=
  Units.ext_iff

theorem hilbert90_apply_eq_iff {z u : Eˣ} : hilbert90 c z = u ↔ (u : E) * c z = z :=
  div_eq_iff_eq_mul.trans (Units.ext_iff.trans eq_comm)

theorem descendToNormOne_hilbert90 (χ : Eˣ →* Circle) (hχ : ∀ z : Eˣ, c z = z → χ z = 1)
    (z : Eˣ) : descendToNormOne c χ hχ ⟨hilbert90 c z, z, rfl⟩ = χ z :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ z

/-- The determinant of a unitary matrix of an invertible Hermitian matrix has norm one. -/
theorem det_mem_normOneSubgroup {ι : Type*} [Fintype ι] [DecidableEq ι] {J : Matrix ι ι E}
    (hJ : Matrix.IsHermitianFor c J) (hJu : IsUnit J.det) (g : ofForm c J) :
    Matrix.GeneralLinearGroup.det (g : GL ι E) ∈ normOneSubgroup c := by
  have := hJ
  have h := congrArg Matrix.det (show ((g : GL ι E) : Matrix ι ι E)ᵀ * J *
    ((g : GL ι E) : Matrix ι ι E).map c = J from g.2)
  rw [det_mul, det_mul, det_transpose,
    show (((g : GL ι E) : Matrix ι ι E).map c).det = c ((g : GL ι E) : Matrix ι ι E).det from
      (c.toRingHom.map_det _).symm] at h
  refine mem_normOneSubgroup.mpr (hJu.mul_left_cancel ?_)
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  linear_combination h

end UnitaryGroup

namespace IsQuadraticInvolution

open UnitaryGroup

section Ring

variable {c} {ξ : E} (h : IsQuadraticInvolution c ξ)
include h

theorem exists_eq (z : E) : ∃ a b : R, z = algebraMap R E a + algebraMap R E b * ξ := by
  obtain ⟨b, h0, h1⟩ := h.exists_basis
  refine ⟨b.repr z 0, b.repr z 1, ?_⟩
  conv_lhs => rw [← b.sum_repr z, Fin.sum_univ_two, h0, h1, Algebra.smul_def, Algebra.smul_def,
    mul_one]

theorem algebraMap_injective : Function.Injective (algebraMap R E) := by
  obtain ⟨b, h0, -⟩ := h.exists_basis
  intro x y hxy
  have : x • b 0 = y • b 0 := by rw [h0, Algebra.smul_def, Algebra.smul_def, hxy]
  simpa using congrArg (fun v => b.repr v 0) this

/-- A quadratic involution is an involution. -/
theorem involutive : Function.Involutive c := by
  intro z
  obtain ⟨a, b, rfl⟩ := h.exists_eq z
  simp [h.map_eq_neg]

theorem finrank_eq_two [StrongRankCondition R] : Module.finrank R E = 2 := by
  obtain ⟨b, -, -⟩ := h.exists_basis
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

theorem finite : Module.Finite R E := by
  obtain ⟨b, -, -⟩ := h.exists_basis
  exact Module.Finite.of_basis b

theorem range_hilbert90_le_normOneSubgroup : (hilbert90 c).range ≤ normOneSubgroup c := by
  rintro u ⟨z, hz⟩
  have h1 := hilbert90_apply_eq_iff.mp hz
  have h2 := congrArg c h1
  rw [map_mul, h.involutive] at h2
  refine mem_normOneSubgroup.mpr (z.isUnit.mul_right_cancel ?_)
  rw [mul_assoc, h2, h1, one_mul]

section Two

variable [Invertible (2 : R)]

/-- An element fixed by `c` comes from `R`. -/
theorem exists_of_fixed {z : E} (hz : c z = z) : ∃ a : R, z = algebraMap R E a := by
  obtain ⟨a, b, rfl⟩ := h.exists_eq z
  refine ⟨a, ?_⟩
  have h2 : algebraMap R E (⅟(2 : R)) * 2 = 1 := by
    rw [← map_ofNat (algebraMap R E) 2, ← map_mul, invOf_mul_self, map_one]
  rw [map_add, map_mul, c.commutes, c.commutes, h.map_eq_neg] at hz
  linear_combination (-algebraMap R E (⅟(2 : R))) * hz - algebraMap R E b * ξ * h2

theorem exists_unit_of_fixed {z : Eˣ} (hz : c z = z) :
    ∃ a : Rˣ, z = Units.map (algebraMap R E : R →* E) a := by
  have hz' : c (z⁻¹ : Eˣ) = (z⁻¹ : Eˣ) := by
    refine z.isUnit.mul_left_cancel ?_
    conv_lhs => rw [← hz, ← map_mul]
    rw [Units.mul_inv, map_one]
  obtain ⟨a, ha⟩ := h.exists_of_fixed hz
  obtain ⟨a', ha'⟩ := h.exists_of_fixed hz'
  have : a * a' = 1 := h.algebraMap_injective (by rw [map_mul, ← ha, ← ha', Units.mul_inv, map_one])
  exact ⟨Units.mkOfMulEqOne a a' this, Units.ext ha⟩

/-- A character of `Eˣ` trivial on `Rˣ` is trivial on the elements fixed by `c`. -/
theorem map_eq_one_of_fixed {χ : Eˣ →* Circle}
    (hχ : ∀ a : Rˣ, χ (Units.map (algebraMap R E : R →* E) a) = 1) (z : Eˣ) (hz : c z = z) :
    χ z = 1 := by
  obtain ⟨a, rfl⟩ := h.exists_unit_of_fixed hz
  exact hχ a

/-- `N_{E/R}(z) = z c(z)`. -/
theorem algebraMap_norm (z : E) : algebraMap R E (Algebra.norm R z) = z * c z := by
  obtain ⟨x, y, rfl⟩ := h.exists_eq z
  obtain ⟨d, hd⟩ := h.exists_of_fixed (z := ξ * ξ) (by rw [map_mul, h.map_eq_neg, neg_mul_neg])
  obtain ⟨b, h0, h1⟩ := h.exists_basis
  have e0 : (algebraMap R E x + algebraMap R E y * ξ) * b 0 = x • b 0 + y • b 1 := by
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def]; ring
  have e1 : (algebraMap R E x + algebraMap R E y * ξ) * b 1 = (y * d) • b 0 + x • b 1 := by
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, map_mul, ← hd]; ring
  rw [Algebra.norm_eq_matrix_det b, det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1]
  simp [h.map_eq_neg, ← hd]
  ring

/-- A character of `Eˣ` trivial on norms takes inverse values at `z` and `c(z)`. -/
theorem map_map_eq_inv {χ : Eˣ →* Circle}
    (hχ : ∀ z : Eˣ, χ (Units.map (algebraMap R E : R →* E)
      (Units.map (Algebra.norm R : E →* R) z)) = 1) (z : Eˣ) :
    χ (Units.map (c : E →* E) z) = (χ z)⁻¹ := by
  have h1 := hχ z
  rw [show Units.map (algebraMap R E : R →* E) (Units.map (Algebra.norm R : E →* R) z) =
      z * Units.map (c : E →* E) z from Units.ext (h.algebraMap_norm z), map_mul] at h1
  exact eq_inv_of_mul_eq_one_right h1

end Two

end Ring

/-- **Hilbert's theorem 90** for a quadratic algebra over a field in which `2` is invertible:
the elements of norm one are the `z / c(z)`. -/
theorem range_hilbert90_eq_normOneSubgroup {R : Type*} [Field R] [Invertible (2 : R)]
    {E : Type*} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {ξ : E}
    (h : IsQuadraticInvolution c ξ) : (hilbert90 c).range = normOneSubgroup c := by
  refine le_antisymm h.range_hilbert90_le_normOneSubgroup fun u hu => ?_
  have hu := mem_normOneSubgroup.mp hu
  obtain ⟨a, b, hab⟩ := h.exists_eq u
  have hc : c u = algebraMap R E a - algebraMap R E b * ξ := by
    rw [hab]; simp [h.map_eq_neg, sub_eq_add_neg]
  by_cases ha : 1 + a = 0
  · have ha' : 1 + algebraMap R E a = 0 := by simpa using congrArg (algebraMap R E) ha
    have hb : algebraMap R E (b * b) * (ξ * ξ) = 0 := by
      rw [hc, hab] at hu
      rw [map_mul]
      linear_combination -hu + (algebraMap R E a - 1) * ha'
    have hb0 : b = 0 := mul_self_eq_zero.mp (h.algebraMap_injective (by
      rw [(h.isUnit.mul h.isUnit).mul_left_eq_zero.mp hb, map_zero]))
    refine ⟨h.isUnit.unit, hilbert90_apply_eq_iff.mpr ?_⟩
    rw [IsUnit.unit_spec, h.map_eq_neg, hab, hb0, map_zero]
    linear_combination (-ξ) * ha'
  · have hz : IsUnit ((1 + (u : E)) * (1 + c u)) := by
      have : (1 + (u : E)) * (1 + c u) = algebraMap R E (2 * (1 + a)) := by
        rw [map_mul, map_add, map_one, map_ofNat]
        linear_combination hu + hab + hc
      rw [this]
      exact (Ne.isUnit (mul_ne_zero (Invertible.ne_zero 2) ha)).map _
    refine ⟨(isUnit_of_mul_isUnit_left hz).unit, hilbert90_apply_eq_iff.mpr ?_⟩
    rw [IsUnit.unit_spec, map_add, map_one]
    linear_combination hu

/-- Over a field, a quadratic involution makes `E` a quadratic extension. -/
theorem isQuadraticExtension {R : Type*} [Field R] {E : Type*} [Field E] [Algebra R E]
    {c : E →ₐ[R] E} {ξ : E} (h : IsQuadraticInvolution c ξ) :
    Algebra.IsQuadraticExtension R E :=
  ⟨h.finrank_eq_two⟩

/-- Over a field in which `2 ≠ 0`, a quadratic involution makes `E` a Galois extension. -/
theorem isGalois {R : Type*} [Field R] [NeZero (2 : R)] {E : Type*} [Field E] [Algebra R E]
    {c : E →ₐ[R] E} {ξ : E} (h : IsQuadraticInvolution c ξ) : IsGalois R E := by
  have := h.isQuadraticExtension
  have : FiniteDimensional R E := h.finite
  have : c ≠ AlgHom.id R E := by
    intro hc
    have h1 := h.map_eq_neg
    rw [hc, AlgHom.id_apply] at h1
    have h2 : (2 : E) * ξ = 0 := by linear_combination h1
    have h3 : (2 : E) ≠ 0 := by
      rw [← map_ofNat (algebraMap R E) 2]
      exact (map_ne_zero _).2 two_ne_zero
    exact h.isUnit.ne_zero ((mul_eq_zero.1 h2).resolve_left h3)
  -- the automorphism group has two elements, so its order is the degree
  let σ : E ≃ₐ[R] E := AlgEquiv.ofAlgHom c c (AlgHom.ext h.involutive) (AlgHom.ext h.involutive)
  have hσ : σ ≠ 1 := fun h1 => this (AlgHom.ext fun z => by
    have := congrArg (fun f : E ≃ₐ[R] E => f z) h1
    simpa [σ] using this)
  have hcard : 2 ≤ Nat.card (E ≃ₐ[R] E) := by
    classical
    rw [Nat.card_eq_fintype_card]
    have : ({1, σ} : Finset (E ≃ₐ[R] E)).card = 2 := Finset.card_pair (Ne.symm hσ)
    rw [← this]
    exact Finset.card_le_univ _
  refine IsGalois.of_card_aut_eq_finrank R E (le_antisymm ?_ ?_)
  · rw [h.finrank_eq_two, Nat.card_eq_fintype_card, ← h.finrank_eq_two]
    exact AlgEquiv.card_le
  · rw [h.finrank_eq_two]; exact hcard

/-- **Hermitian matrices are diagonalizable by congruence**: an invertible Hermitian matrix `b`
over `E` is `a D c(a)ᵀ` with `a` invertible and `D` diagonal with entries in `Rˣ`. -/
theorem exists_eq_mul_diagonal_mul {R : Type*} [Field R] [NeZero (2 : R)] {E : Type*} [Field E]
    [Algebra R E] {c : E →ₐ[R] E} {ξ : E} (h : IsQuadraticInvolution c ξ) {ν : Type*}
    [Fintype ν] [DecidableEq ν] (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) (hdet : b.det ≠ 0) :
    ∃ (a : GL ν E) (D : ν → Rˣ),
      b = (a : Matrix ν ν E) * diagonal (fun j => algebraMap R E (D j)) *
        ((a : Matrix ν ν E).map c)ᵀ := by
  let : Invertible (2 : R) := invertibleOfNonzero two_ne_zero
  have h2 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap R E) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have hG : ∀ x y, (c : E →+* E) (b x y) = b y x := by
    intro x y
    have := congrFun (congrFun hb y) x
    simpa using this
  obtain ⟨P, d, hP, hPd, hfix, hne⟩ :=
    Sesquilinear.exists_congr_diagonal_of_hermitian (c := (c : E →+* E)) h2
      (fun t => h.involutive t) (G := b) hG
  have hd0 := hne hdet
  have hPd' : Pᵀ * b * P.map c = diagonal d := hPd
  choose f hf using fun i => h.exists_of_fixed (hfix i)
  have hf0 : ∀ i, f i ≠ 0 := by
    intro i h; apply hd0 i; rw [hf i, h, map_zero]
  have hQ : (Pᵀ).det ≠ 0 := by rwa [det_transpose]
  set A : Matrix ν ν E := (Pᵀ)⁻¹ with hA
  have hAQ : A * Pᵀ = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hQ)
  have hQA : Pᵀ * A = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hQ)
  have hAs : (A.map c)ᵀ * P.map c = 1 := by
    have h1 : (Pᵀ * A).map c = 1 := by rw [hQA]; exact Matrix.map_one _ (map_zero c) (map_one c)
    rw [show (Pᵀ * A).map c = (Pᵀ).map c * A.map c from Matrix.map_mul (f := c.toRingHom)] at h1
    have h3 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h3
    simpa [Matrix.transpose_map] using h3
  have hAs' : P.map c * (A.map c)ᵀ = 1 := mul_eq_one_comm.mp hAs
  have hAdet : A.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hAQ
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet, fun j => Units.mk0 (f j) (hf0 j), ?_⟩
  have hD : diagonal (fun j => algebraMap R E ((Units.mk0 (f j) (hf0 j) : Rˣ) : R)) =
      diagonal d := by
    congr 1; funext j; simp [hf j]
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  rw [hD, ← hPd']
  calc b = (A * Pᵀ) * b * (P.map c * (A.map c)ᵀ) := by
        rw [hAQ, hAs', Matrix.one_mul, Matrix.mul_one]
    _ = A * (Pᵀ * b * P.map c) * (A.map c)ᵀ := by simp only [Matrix.mul_assoc]

end IsQuadraticInvolution

end Langlands
