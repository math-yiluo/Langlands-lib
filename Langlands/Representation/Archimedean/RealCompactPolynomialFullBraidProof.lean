import Langlands.Representation.Archimedean.RealCompactPolynomialCornerInterpolation
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Laurent

/-! # The full compact central-factorial braid -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealCompactPolynomialFullBraidProof

open AddMonoidAlgebra RealCompactPolynomialRelations

section Laurent

variable {R : Type*} [Ring R]

private def BoundedAbove (p : LaurentPolynomial R) (m : ℤ) : Prop :=
  ∀ k ∈ p.coeff.support, k ≤ m

private theorem BoundedAbove.coeff_eq_zero {p : LaurentPolynomial R} {m k : ℤ}
    (hp : BoundedAbove p m) (hk : m < k) : p.coeff k = 0 :=
  Finsupp.notMem_support_iff.mp fun h => (hp k h).not_gt hk

private theorem BoundedAbove.of_coeff_eq_zero {p : LaurentPolynomial R} {m : ℤ}
    (hp : ∀ k, m < k → p.coeff k = 0) : BoundedAbove p m := by
  intro k hk
  exact le_of_not_gt fun h => Finsupp.mem_support_iff.mp hk (hp k h)

private theorem BoundedAbove.single (k : ℤ) (r : R) :
    BoundedAbove (.single k r : LaurentPolynomial R) k := by
  intro j hj
  exact (Finset.mem_singleton.mp (Finsupp.support_single_subset hj)).le

private theorem BoundedAbove.mono {p : LaurentPolynomial R} {m n : ℤ}
    (hp : BoundedAbove p m) (h : m ≤ n) : BoundedAbove p n :=
  fun k hk => (hp k hk).trans h

private theorem BoundedAbove.add {p q : LaurentPolynomial R} {m : ℤ}
    (hp : BoundedAbove p m) (hq : BoundedAbove q m) : BoundedAbove (p + q) m := by
  apply BoundedAbove.of_coeff_eq_zero
  intro k hk
  simp [hp.coeff_eq_zero hk, hq.coeff_eq_zero hk]

private theorem BoundedAbove.sub {p q : LaurentPolynomial R} {m : ℤ}
    (hp : BoundedAbove p m) (hq : BoundedAbove q m) : BoundedAbove (p - q) m := by
  apply BoundedAbove.of_coeff_eq_zero
  intro k hk
  simp [hp.coeff_eq_zero hk, hq.coeff_eq_zero hk]

private theorem BoundedAbove.smul [Algebra ℂ R] {p : LaurentPolynomial R} {m : ℤ}
    (hp : BoundedAbove p m) (c : ℂ) : BoundedAbove (c • p) m := by
  apply BoundedAbove.of_coeff_eq_zero
  intro k hk
  simp [hp.coeff_eq_zero hk]

private theorem BoundedAbove.mul {p q : LaurentPolynomial R} {m n : ℤ}
    (hp : BoundedAbove p m) (hq : BoundedAbove q n) : BoundedAbove (p * q) (m + n) := by
  apply BoundedAbove.of_coeff_eq_zero
  intro k hk
  simp only [coeff_mul, Finsupp.sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ite_eq_right ?_
  have := hp i hi
  have := hq j hj
  omega

private theorem BoundedAbove.coeff_mul {p q : LaurentPolynomial R} {m n : ℤ}
    (hp : BoundedAbove p m) (hq : BoundedAbove q n) :
    (p * q).coeff (m + n) = p.coeff m * q.coeff n := by
  apply coeff_mul_add_of_uniqueAdd
  intro i j hi hj he
  have := hp i hi
  have := hq j hj
  omega

private theorem support_max {q : LaurentPolynomial R} (hq : q ≠ 0) :
    ∃ n, BoundedAbove q n ∧ q.coeff n ≠ 0 := by
  have hs : q.coeff.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (fun h => hq (coeff_injective (h.trans coeff_zero.symm)))
  exact ⟨_, fun _ hk => Finset.le_max' _ _ hk, Finsupp.mem_support_iff.mp (Finset.max'_mem _ hs)⟩

private theorem regular_of_unit_top {p : LaurentPolynomial R} {m : ℤ}
    (hp : BoundedAbove p m) (hu : IsUnit (p.coeff m)) : IsRegular p := by
  constructor
  · intro q r h
    by_contra hne
    obtain ⟨n, hn, hn0⟩ := support_max (sub_ne_zero.mpr hne : q - r ≠ 0)
    have hz : p * (q - r) = 0 := by simpa [mul_sub] using sub_eq_zero.mpr h
    have ht := congrArg (fun z : LaurentPolynomial R => z.coeff (m + n)) hz
    rw [hp.coeff_mul hn, coeff_zero] at ht
    exact hn0 (hu.isRegular.left (ht.trans (mul_zero _).symm))
  · intro q r h
    by_contra hne
    obtain ⟨n, hn, hn0⟩ := support_max (sub_ne_zero.mpr hne : q - r ≠ 0)
    have hz : (q - r) * p = 0 := by simpa [sub_mul] using sub_eq_zero.mpr h
    have ht := congrArg (fun z : LaurentPolynomial R => z.coeff (n + m)) hz
    rw [hn.coeff_mul hp, coeff_zero] at ht
    exact hn0 (hu.isRegular.right (ht.trans (zero_mul _).symm))

variable [Algebra ℂ R]

private theorem factor_top {p : LaurentPolynomial R} (hp : BoundedAbove p 1) (n : ℕ) :
    BoundedAbove (factor p n) n ∧ (factor p n).coeff n = p.coeff 1 ^ n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp only [factor, ← LaurentPolynomial.single_zero_one_eq_one, Nat.cast_zero, pow_zero]
      exact ⟨BoundedAbove.single 0 (1 : R), Finsupp.single_eq_same⟩
  | one => exact ⟨hp, by simp [factor]⟩
  | more n ih _ =>
      have hp2 : BoundedAbove (p * p) 2 := hp.mul hp
      have hsum : BoundedAbove (p * p + algebraMap ℂ (LaurentPolynomial R) ((n + 1 : ℂ) ^ 2)) 2 :=
        hp2.add ((BoundedAbove.single 0 (algebraMap ℂ R ((n + 1 : ℂ) ^ 2))).mono (by decide))
      have hscalar : (algebraMap ℂ (LaurentPolynomial R) ((n + 1 : ℂ) ^ 2)).coeff 2 = 0 := by
        simp only [LaurentPolynomial.algebraMap_apply, LaurentPolynomial.C_apply]
        rfl
      rw [factor_add_two, Nat.cast_add, Nat.cast_ofNat, add_comm (n : ℤ) 2]
      refine ⟨hsum.mul ih.1, ?_⟩
      rw [hsum.coeff_mul ih.1, coeff_add, Finsupp.add_apply, hscalar, add_zero, ih.2,
        show (2 : ℤ) = 1 + 1 by decide, hp.coeff_mul hp, ← pow_two, ← pow_add]
      rw [Nat.add_comm]

private theorem factor_regular {p : LaurentPolynomial R} (hp : BoundedAbove p 1)
    (hu : IsUnit (p.coeff 1)) (n : ℕ) : IsRegular (factor p n) :=
  regular_of_unit_top (factor_top hp n).1 ((factor_top hp n).2 ▸ hu.pow n)

private def augment : LaurentPolynomial R →ₐ[ℂ] R :=
  liftNCAlgHom (AlgHom.id ℂ R) (1 : Multiplicative ℤ →* R) (fun _ _ => Commute.one_right _)

@[simp] private theorem augment_single (n : ℤ) (r : R) :
    augment (.single n r : LaurentPolynomial R) = r := by
  change liftNC (AlgHom.id ℂ R).toRingHom.toAddMonoidHom (1 : Multiplicative ℤ →* R)
    (single n r) = r
  rw [liftNC_single]
  exact mul_one r

end Laurent

section Commutators

variable {R : Type*} [Ring R] [Algebra ℂ R]

private theorem smul_commutator (c d : ℂ) (p q : R) :
    (c • p) * (d • q) - (d • q) * (c • p) = (c * d) • (p * q - q * p) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm d c, smul_sub]

private theorem commute_smul_sub {p e f : R} (he : Commute p e) (hf : Commute p f) (c : ℂ) :
    Commute p (c • (e - f)) :=
  (he.sub_right hf).smul_right c

private theorem compact_XY {e f h : R} (hEF : e * f - f * e = h) :
    ((1 / 2 : ℂ) • (e - f)) * ((Complex.I / 2) • (e + f)) -
      ((Complex.I / 2) • (e + f)) * ((1 / 2 : ℂ) • (e - f)) = (Complex.I / 2) • h := by
  have h₂ : (e - f) * (e + f) - (e + f) * (e - f) = (2 : ℂ) • h := by
    rw [← hEF, two_smul]
    noncomm_ring
  rw [smul_commutator, h₂, smul_smul]
  congr 1
  ring

private theorem compact_ZX {e f h : R} (hHE : h * e - e * h = (2 : ℂ) • e)
    (hHF : h * f - f * h = (-2 : ℂ) • f) :
    ((Complex.I / 2) • h) * ((1 / 2 : ℂ) • (e - f)) -
      ((1 / 2 : ℂ) • (e - f)) * ((Complex.I / 2) • h) = (Complex.I / 2) • (e + f) := by
  have h₂ : h * (e - f) - (e - f) * h = (2 : ℂ) • e - (-2 : ℂ) • f := by
    rw [← hHE, ← hHF]
    noncomm_ring
  rw [smul_commutator, h₂, neg_smul (2 : ℂ) f, sub_neg_eq_add, ← smul_add, smul_smul]
  congr 1
  ring

private theorem compact_ZY {e f h : R} (hHE : h * e - e * h = (2 : ℂ) • e)
    (hHF : h * f - f * h = (-2 : ℂ) • f) :
    ((Complex.I / 2) • h) * ((Complex.I / 2) • (e + f)) -
      ((Complex.I / 2) • (e + f)) * ((Complex.I / 2) • h) = -((1 / 2 : ℂ) • (e - f)) := by
  have h₂ : h * (e + f) - (e + f) * h = (2 : ℂ) • e + (-2 : ℂ) • f := by
    rw [← hHE, ← hHF]
    noncomm_ring
  rw [smul_commutator, h₂, neg_smul (2 : ℂ) f, ← sub_eq_add_neg, ← smul_sub,
    smul_smul, ← neg_smul (1 / 2 : ℂ) (e - f)]
  congr 1
  calc
    (Complex.I / 2 * (Complex.I / 2)) * 2 = (Complex.I * Complex.I) / 2 := by ring
    _ = -(1 / 2) := by rw [Complex.I_mul_I, neg_div]

omit [Algebra ℂ R] in
private theorem neg_left_commutator {p q r : R} (h : p * q - q * p = r) :
    (-p) * q - q * (-p) = -r := by
  linear_combination (norm := noncomm_ring) -h

omit [Algebra ℂ R] in
private theorem neg_left_commutator_of_eq_neg {p q r : R} (h : p * q - q * p = -r) :
    (-p) * q - q * (-p) = r := by
  simpa only [neg_neg] using neg_left_commutator h

end Commutators

section Sequences

variable {A : Type*} [Ring A] [Algebra ℂ A]

private abbrev Operators (A : Type*) [Ring A] [Algebra ℂ A] := Module.End ℂ (ℤ → A)

private def left : A →ₐ[ℂ] Operators A where
  toFun x :=
    { toFun := fun f n => x * f n
      map_add' := fun f g => funext fun n => mul_add x (f n) (g n)
      map_smul' := fun c f => funext fun n => mul_smul_comm c x (f n) }
  map_one' := by ext f n; exact one_mul (f n)
  map_mul' x y := by ext f n; exact mul_assoc x y (f n)
  map_zero' := by ext f n; exact zero_mul (f n)
  map_add' x y := by ext f n; exact add_mul x y (f n)
  commutes' c := by
    ext f n
    exact (Algebra.smul_def c (f n)).symm

private def shiftEquiv (A : Type*) [Ring A] [Algebra ℂ A] : (ℤ → A) ≃ₗ[ℂ] (ℤ → A) where
  toFun f n := f (n - 1)
  invFun f n := f (n + 1)
  left_inv f := funext fun n => congrArg f (by omega)
  right_inv f := funext fun n => congrArg f (by omega)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def shift (A : Type*) [Ring A] [Algebra ℂ A] : Operators A :=
  (shiftEquiv A).toLinearMap

private theorem isUnit_shift (A : Type*) [Ring A] [Algebra ℂ A] : IsUnit (shift A) :=
  ⟨⟨shift A, (shiftEquiv A).symm.toLinearMap,
    LinearMap.ext (shiftEquiv A).apply_symm_apply,
    LinearMap.ext (shiftEquiv A).symm_apply_apply⟩, rfl⟩

private def lower (A : Type*) [Ring A] [Algebra ℂ A] : Operators A where
  toFun f n := (-((n : ℂ) + 1) * n) • f (n + 1)
  map_add' f g := funext fun n => smul_add _ (f (n + 1)) (g (n + 1))
  map_smul' c f := funext fun n => smul_comm _ c (f (n + 1))

private def weight (A : Type*) [Ring A] [Algebra ℂ A] : Operators A where
  toFun f n := (2 * (n : ℂ)) • f n
  map_add' f g := funext fun n => smul_add _ (f n) (g n)
  map_smul' c f := funext fun n => smul_comm _ c (f n)

private theorem shift_lower : shift A * lower A - lower A * shift A = weight A := by
  ext f n
  change (-(((n - 1 : ℤ) : ℂ) + 1) * ((n - 1 : ℤ) : ℂ)) • f (n - 1 + 1) -
    (-((n : ℂ) + 1) * n) • f (n + 1 - 1) = (2 * (n : ℂ)) • f n
  rw [sub_add_cancel, add_sub_cancel_right, ← sub_smul]
  congr 1
  push_cast
  ring

private theorem weight_shift : weight A * shift A - shift A * weight A = (2 : ℂ) • shift A := by
  ext f n
  change (2 * (n : ℂ)) • f (n - 1) - (2 * ((n - 1 : ℤ) : ℂ)) • f (n - 1) =
    (2 : ℂ) • f (n - 1)
  rw [← sub_smul]
  congr 1
  push_cast
  ring

private theorem weight_lower : weight A * lower A - lower A * weight A =
    (-2 : ℂ) • lower A := by
  ext f n
  change (2 * (n : ℂ)) • ((-((n : ℂ) + 1) * n) • f (n + 1)) -
    (-((n : ℂ) + 1) * n) • ((2 * ((n + 1 : ℤ) : ℂ)) • f (n + 1)) =
    (-2 : ℂ) • ((-((n : ℂ) + 1) * n) • f (n + 1))
  simp only [smul_smul, ← sub_smul, Int.cast_add, Int.cast_one]
  congr 1
  ring

private theorem left_shift (x : A) : Commute (left x) (shift A) := rfl

private theorem left_lower (x : A) : Commute (left x) (lower A) := by
  show left x * lower A = lower A * left x
  ext f n
  exact mul_smul_comm _ x (f (n + 1))

private theorem left_weight (x : A) : Commute (left x) (weight A) := by
  show left x * weight A = weight A * left x
  ext f n
  exact mul_smul_comm _ x (f n)

private abbrev Extension (A : Type*) [Ring A] [Algebra ℂ A] := LaurentPolynomial (Operators A)

private def constant : A →ₐ[ℂ] Extension A :=
  singleZeroAlgHom.comp left

private def E (A : Type*) [Ring A] [Algebra ℂ A] : Extension A :=
  .single 1 (shift A)

private def F (A : Type*) [Ring A] [Algebra ℂ A] : Extension A :=
  .single (-1) (lower A)

private def H (A : Type*) [Ring A] [Algebra ℂ A] : Extension A :=
  .single 0 (weight A)

private theorem commutator_EF : E A * F A - F A * E A = H A := by
  simp only [E, F, H, single_mul_single, add_neg_cancel, neg_add_cancel,
    ← single_sub, shift_lower]

private theorem commutator_HE : H A * E A - E A * H A = (2 : ℂ) • E A := by
  simp only [E, H, single_mul_single, zero_add, add_zero, ← single_sub,
    weight_shift, smul_single]

private theorem commutator_HF : H A * F A - F A * H A = (-2 : ℂ) • F A := by
  simp only [F, H, single_mul_single, zero_add, add_zero, ← single_sub,
    weight_lower, smul_single]

private theorem constant_commutes (x : A) {d : Operators A} (k : ℤ)
    (h : Commute (left x) d) : Commute (constant x) (.single k d) := by
  show single 0 (left x) * single k d = single k d * single 0 (left x)
  simp only [single_mul_single, zero_add, add_zero, h.eq]

private def rotationX (A : Type*) [Ring A] [Algebra ℂ A] : Extension A :=
  (1 / 2 : ℂ) • (E A - F A)

private def rotationY (A : Type*) [Ring A] [Algebra ℂ A] : Extension A :=
  (Complex.I / 2) • (E A + F A)

private def rotationZ (A : Type*) [Ring A] [Algebra ℂ A] : Extension A :=
  (Complex.I / 2) • H A

private def liftedX (x : A) : Extension A := constant x + rotationX A
private def liftedY (y : A) : Extension A := constant y + rotationY A
private def liftedZ (z : A) : Extension A := constant z + rotationZ A

private theorem constant_commutes_X (x : A) : Commute (constant x) (rotationX A) := by
  have he : Commute (constant x) (E A) := constant_commutes x 1 (left_shift x)
  have hf : Commute (constant x) (F A) := constant_commutes x (-1) (left_lower x)
  exact commute_smul_sub (R := Extension A) (p := constant x) (e := E A) (f := F A)
    he hf (1 / 2)

private theorem constant_commutes_Y (x : A) : Commute (constant x) (rotationY A) :=
  ((constant_commutes x 1 (left_shift x)).add_right
    (constant_commutes x (-1) (left_lower x))).smul_right _

private theorem constant_commutes_Z (x : A) : Commute (constant x) (rotationZ A) :=
  (constant_commutes x 0 (left_weight x)).smul_right _

private theorem add_commutators {p q r s : Extension A} (hps : Commute p s)
    (hqr : Commute q r) :
    (p + q) * (r + s) - (r + s) * (p + q) = (p * r - r * p) + (q * s - s * q) := by
  linear_combination (norm := noncomm_ring) hps.eq + hqr.eq

private theorem constant_commutator {x y z : A} (h : x * y - y * x = z) :
    constant x * constant y - constant y * constant x = constant z := by
  simpa only [map_sub, map_mul] using congrArg (constant (A := A)) h

private theorem lifted_XY {x y z : A} (h : x * y - y * x = z) :
    liftedX x * liftedY y - liftedY y * liftedX x = liftedZ z := by
  have hrotation : rotationX A * rotationY A - rotationY A * rotationX A = rotationZ A :=
    compact_XY (R := Extension A) (e := E A) (f := F A) (h := H A) commutator_EF
  rw [liftedX, liftedY, liftedZ,
    add_commutators (constant_commutes_Y x) (constant_commutes_X y).symm,
    constant_commutator h, hrotation]

private theorem lifted_ZX {x y z : A} (h : z * x - x * z = y) :
    liftedZ z * liftedX x - liftedX x * liftedZ z = liftedY y := by
  have hrotation : rotationZ A * rotationX A - rotationX A * rotationZ A = rotationY A :=
    compact_ZX (R := Extension A) (e := E A) (f := F A) (h := H A)
      commutator_HE commutator_HF
  rw [liftedZ, liftedX, liftedY,
    add_commutators (constant_commutes_X z) (constant_commutes_Z x).symm,
    constant_commutator h, hrotation]

private theorem lifted_ZY {x y z : A} (h : z * y - y * z = -x) :
    liftedZ z * liftedY y - liftedY y * liftedZ z = -liftedX x := by
  have hrotation :
      rotationZ A * rotationY A - rotationY A * rotationZ A = -rotationX A :=
    compact_ZY (R := Extension A) (e := E A) (f := F A) (h := H A)
      commutator_HE commutator_HF
  rw [liftedZ, liftedY, liftedX,
    add_commutators (constant_commutes_Y z) (constant_commutes_Z y).symm,
    constant_commutator h, hrotation, map_neg]
  abel

private theorem constant_bounded (x : A) : BoundedAbove (constant x) 1 :=
  (BoundedAbove.single 0 (left x)).mono (by decide)

private theorem E_bounded : BoundedAbove (E A) 1 :=
  BoundedAbove.single 1 (shift A)

private theorem F_bounded : BoundedAbove (F A) 1 :=
  (BoundedAbove.single (-1) (lower A)).mono (by decide)

private theorem isUnit_smul_shift (c : ℂ) (hc : c ≠ 0) : IsUnit (c • shift A) := by
  rw [Algebra.smul_def]
  exact ((isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ (Operators A))).mul (isUnit_shift A)

private theorem liftedX_regular (x : A) (n : ℕ) : IsRegular (factor (liftedX x) n) := by
  have hb : BoundedAbove (liftedX x) 1 :=
    (constant_bounded x).add ((E_bounded.sub F_bounded).smul (1 / 2 : ℂ))
  have ht : (liftedX x).coeff 1 = (1 / 2 : ℂ) • shift A := by
    change (single 0 (left x) + (1 / 2 : ℂ) •
      ((single 1 (shift A) : Extension A) - single (-1) (lower A))).coeff 1 = _
    simp only [coeff_add, Finsupp.add_apply, coeff_smul_apply, coeff_sub,
      Finsupp.sub_apply, coeff_single, Finsupp.single_apply]
    norm_num
  apply factor_regular hb _ n
  rw [ht]
  exact isUnit_smul_shift _ (by norm_num)

private theorem liftedY_regular (y : A) (n : ℕ) : IsRegular (factor (liftedY y) n) := by
  have hb : BoundedAbove (liftedY y) 1 :=
    (constant_bounded y).add ((E_bounded.add F_bounded).smul (Complex.I / 2))
  have ht : (liftedY y).coeff 1 = (Complex.I / 2) • shift A := by
    change (single 0 (left y) + (Complex.I / 2) •
      ((single 1 (shift A) : Extension A) + single (-1) (lower A))).coeff 1 = _
    simp only [coeff_add, Finsupp.add_apply, coeff_smul_apply, coeff_single, Finsupp.single_apply]
    norm_num
  apply factor_regular hb _ n
  rw [ht]
  exact isUnit_smul_shift _ (div_ne_zero Complex.I_ne_zero (by norm_num))

private def VanishesBelowZero (f : ℤ → A) : Prop := ∀ n < 0, f n = 0

private def Descends (p : Operators A) (x : A) : Prop :=
  ∀ f : ℤ → A, VanishesBelowZero f → VanishesBelowZero (p f) ∧ p f 0 = x * f 0

private theorem Descends.one : Descends (1 : Operators A) (1 : A) := by
  intro f hf
  exact ⟨hf, (one_mul (f 0)).symm⟩

private theorem Descends.add {p q : Operators A} {x y : A}
    (hp : Descends p x) (hq : Descends q y) : Descends (p + q) (x + y) := by
  intro f hf
  obtain ⟨hp', hp0⟩ := hp f hf
  obtain ⟨hq', hq0⟩ := hq f hf
  refine ⟨fun n hn => ?_, ?_⟩
  · change p f n + q f n = 0
    rw [hp' n hn, hq' n hn, add_zero]
  · change p f 0 + q f 0 = (x + y) * f 0
    rw [hp0, hq0, add_mul]

private theorem Descends.sub {p q : Operators A} {x y : A}
    (hp : Descends p x) (hq : Descends q y) : Descends (p - q) (x - y) := by
  intro f hf
  obtain ⟨hp', hp0⟩ := hp f hf
  obtain ⟨hq', hq0⟩ := hq f hf
  refine ⟨fun n hn => ?_, ?_⟩
  · change p f n - q f n = 0
    rw [hp' n hn, hq' n hn, sub_zero]
  · change p f 0 - q f 0 = (x - y) * f 0
    rw [hp0, hq0, sub_mul]

private theorem Descends.mul {p q : Operators A} {x y : A}
    (hp : Descends p x) (hq : Descends q y) : Descends (p * q) (x * y) := by
  intro f hf
  obtain ⟨hq', hq0⟩ := hq f hf
  obtain ⟨hp', hp0⟩ := hp (q f) hq'
  exact ⟨hp', by rw [Module.End.mul_apply, hp0, hq0, mul_assoc]⟩

private theorem Descends.smul {p : Operators A} {x : A}
    (hp : Descends p x) (c : ℂ) : Descends (c • p) (c • x) := by
  intro f hf
  obtain ⟨hp', hp0⟩ := hp f hf
  refine ⟨fun n hn => ?_, ?_⟩
  · change c • p f n = 0
    rw [hp' n hn, smul_zero]
  · change c • p f 0 = (c • x) * f 0
    rw [hp0, smul_mul_assoc]

private theorem Descends.factor {p : Operators A} {x : A}
    (hp : Descends p x) (n : ℕ) : Descends (factor p n) (factor x n) := by
  induction n using Nat.twoStepInduction with
  | zero => exact Descends.one
  | one => exact hp
  | more n ih _ => exact ((hp.mul hp).mul ih).add (ih.smul ((n + 1 : ℂ) ^ 2))

private theorem Descends.eq {p : Operators A} {x y : A} (hx : Descends p x)
    (hy : Descends p y) : x = y := by
  let f : ℤ → A := fun n => if n = 0 then 1 else 0
  have hf : VanishesBelowZero f := fun n hn => ite_eq_right hn.ne
  simpa [f] using (hx f hf).2.symm.trans (hy f hf).2

private theorem left_descends (x : A) : Descends (left x) x := by
  intro f hf
  exact ⟨fun n hn => by change x * f n = 0; rw [hf n hn, mul_zero], rfl⟩

private theorem shift_descends : Descends (shift A) (0 : A) := by
  intro f hf
  refine ⟨fun n hn => hf (n - 1) (by omega), ?_⟩
  change f (0 - 1) = 0 * f 0
  rw [hf _ (by decide), zero_mul]

private theorem lower_descends : Descends (lower A) (0 : A) := by
  intro f hf
  refine ⟨fun n hn => ?_, ?_⟩
  · change (-((n : ℂ) + 1) * n) • f (n + 1) = 0
    by_cases h : n = -1
    · subst n
      norm_num
    · rw [hf (n + 1) (by omega), smul_zero]
  · change (-(((0 : ℤ) : ℂ) + 1) * ((0 : ℤ) : ℂ)) • f (0 + 1) = 0 * f 0
    norm_num

private theorem liftedX_descends (x : A) : Descends (augment (liftedX x)) x := by
  have h := (left_descends x).add ((shift_descends.sub lower_descends).smul (1 / 2 : ℂ))
  change Descends
    (augment (single 0 (left x) + (1 / 2 : ℂ) • (single 1 (shift A) - single (-1) (lower A)))) x
  simpa only [map_add, map_sub, map_smul, augment_single, sub_zero, smul_zero, add_zero] using h

private theorem liftedY_descends (y : A) : Descends (augment (liftedY y)) y := by
  have h := (left_descends y).add ((shift_descends.add lower_descends).smul (Complex.I / 2))
  change Descends
    (augment (single 0 (left y) + (Complex.I / 2) • (single 1 (shift A) + single (-1) (lower A)))) y
  simpa only [map_add, map_smul, augment_single, smul_zero, add_zero] using h

private theorem map_factor {B : Type*} [Ring B] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) (x : A) (n : ℕ) : φ (factor x n) = factor (φ x) n := by
  induction n using Nat.twoStepInduction with
  | zero => exact map_one φ
  | one => rfl
  | more n ih _ => simp only [factor, map_add, map_mul, map_smul, ih]

private theorem braid_descends {x y : A} (a b : ℕ)
    (h : factor (liftedX x) a * factor (liftedY y) (a + b) * factor (liftedX x) b =
      factor (liftedY y) b * factor (liftedX x) (a + b) * factor (liftedY y) a) :
    factor x a * factor y (a + b) * factor x b =
      factor y b * factor x (a + b) * factor y a := by
  have hAugment := congrArg (augment (R := Operators A)) h
  simp only [map_mul, map_factor] at hAugment
  have hx := liftedX_descends x
  have hy := liftedY_descends y
  have hLeft := ((hx.factor a).mul (hy.factor (a + b))).mul (hx.factor b)
  have hRight := ((hy.factor b).mul (hx.factor (a + b))).mul (hy.factor a)
  rw [hAugment] at hLeft
  exact hLeft.eq hRight

end Sequences

open RealCompactPolynomialFullBraid RealCompactPolynomialCornerInterpolation

private theorem braid_at (a : ℕ) :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (x y z : A),
      x * y - y * x = z → z * x - x * z = y → z * y - y * z = -x →
      ∀ b : ℕ, factor x a * factor y (a + b) * factor x b =
        factor y b * factor x (a + b) * factor y a := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro A _ _ x y z hxy hzx hzy b
    let X := liftedX x
    let Y := liftedY y
    let Z := liftedZ z
    have hXY : X * Y - Y * X = Z := lifted_XY hxy
    have hZX : Z * X - X * Z = Y := lifted_ZX hzx
    have hZY : Z * Y - Y * Z = -X := lifted_ZY hzy
    have hYX : Y * X - X * Y = -Z := by
      linear_combination (norm := noncomm_ring) -hXY
    have hNegZY : (-Z) * Y - Y * (-Z) = X :=
      neg_left_commutator_of_eq_neg (R := Extension A) (p := Z) (q := Y) (r := X) hZY
    have hNegZX : (-Z) * X - X * (-Z) = -Y :=
      neg_left_commutator (R := Extension A) (p := Z) (q := X) (r := Y) hZX
    have hN : normalLeft X Y Z a (b : ℂ) = normalRight X Y Z a (b : ℂ) := by
      apply normal_eq_of_small a
      intro c
      have hc := (ih c.val c.isLt (Extension A) Y X (-Z) hYX hNegZY hNegZX a).symm
      rw [Nat.add_comm c.val a, left_factorization hXY hZY a c.val,
        mul_assoc (factor Y c.val) (factor X (a + c.val)) (factor Y a),
        right_factorization hXY hZX a c.val] at hc
      exact (liftedY_regular y c.val).left
        ((liftedX_regular x c.val).right (by simpa only [mul_assoc] using hc))
    exact braid_descends a b (braid_of_normal_eq hXY hZX hZY a b hN)

end RealCompactPolynomialFullBraidProof

/-- The two-parameter compact braid holds in every complex associative unital algebra. -/
theorem realCompactPolynomialFullBraid : RealCompactPolynomialFullBraidStatement := by
  intro A _ _ x y z hxy hzx hzy a b
  exact RealCompactPolynomialFullBraidProof.braid_at a A x y z hxy hzx hzy b

end Langlands.Archimedean
