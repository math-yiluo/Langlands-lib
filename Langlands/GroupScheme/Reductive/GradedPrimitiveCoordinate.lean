import Langlands.GroupScheme.Rational.TorusWeightPrimitive
import Langlands.CommutativeAlgebra.GradedLineLocal

/-! # Primitive coordinates on a positively graded affine line -/

noncomputable section

universe u

open CategoryTheory Polynomial

namespace Langlands.GroupScheme.Corepresented.GradedPrimitive

variable {R : CommRingCat.{u}} (A : CommAlgCat.{u} R) (d : ℕ)

/-- Exponents zero and at least the first positive degree. -/
def gapMonoid : AddSubmonoid ℤ where
  carrier := {n | n = 0 ∨ (d : ℤ) ≤ n}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro a b (rfl | ha) (rfl | hb)
    · exact Or.inl rfl
    · exact Or.inr (by simpa using hb)
    · exact Or.inr (by simpa using ha)
    · exact Or.inr (by omega)

/-- Laurent polynomials whose positive exponents start in degree `d`. -/
def gapAlgebra : Subalgebra R (LaurentPolynomial A) where
  carrier := {p | ∀ n ∉ gapMonoid d, p.coeff n = 0}
  mul_mem' {p q} hp hq n hn := coeff_mul_eq_zero_of fun i j hij hi hj =>
    hn (hij ▸ (gapMonoid d).add_mem
      (by_contra fun h => hi (hp i h)) (by_contra fun h => hj (hq j h)))
  add_mem' {p q} hp hq n hn := by
    change (p + q).coeff n = 0
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp n hn, hq n hn, add_zero]
  algebraMap_mem' r n hn := by
    rw [LaurentPolynomial.algebraMap_apply, LaurentPolynomial.C_apply]
    split_ifs with h
    · exact False.elim (hn (Or.inl h))
    · rfl

variable {A d}

theorem coeff_zero_mul (hd : 0 < d) (p q : gapAlgebra A d) :
    ((p : LaurentPolynomial A) * q).coeff 0 =
      (p : LaurentPolynomial A).coeff 0 * (q : LaurentPolynomial A).coeff 0 := by
  classical
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum, Finset.sum_eq_single 0]
  · simp
  · intro n _ hn
    by_cases hp : (p : LaurentPolynomial A).coeff n = 0
    · rw [hp, zero_mul]
    have hn' : (d : ℤ) ≤ n := by
      have hm : n ∈ gapMonoid d := by_contra fun h => hp (p.property n h)
      exact hm.resolve_left hn
    have hneg : -n ∉ gapMonoid d := by
      rintro (h | h) <;> omega
    rw [add_zero, q.property (-n) hneg, mul_zero]
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, zero_mul]

theorem coeff_degree_mul (hd : 0 < d) (p q : gapAlgebra A d) :
    ((p : LaurentPolynomial A) * q).coeff d =
      (p : LaurentPolynomial A).coeff 0 * (q : LaurentPolynomial A).coeff d +
      (p : LaurentPolynomial A).coeff d * (q : LaurentPolynomial A).coeff 0 := by
  classical
  have hd' : (d : ℤ) ≠ 0 := by omega
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum,
    Finset.sum_eq_add (0 : ℤ) (d : ℤ) hd'.symm]
  · simp
  · rintro n _ ⟨hn0, hnd⟩
    by_cases hp : (p : LaurentPolynomial A).coeff n = 0
    · rw [hp, zero_mul]
    by_cases hq : (q : LaurentPolynomial A).coeff (-n + d) = 0
    · rw [hq, mul_zero]
    have hn : (d : ℤ) ≤ n := by
      have hm : n ∈ gapMonoid d := by_contra fun h => hp (p.property n h)
      exact hm.resolve_left hn0
    have hn' : (d : ℤ) ≤ -n + d := by
      have hm : -n + d ∈ gapMonoid d := by_contra fun h => hq (q.property _ h)
      exact hm.resolve_left (by omega)
    omega
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, zero_mul]
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, zero_mul]

/-- The constant and first positive coefficients give a dual-number algebra map. -/
def dualCoeffHom (hd : 0 < d) : gapAlgebra A d →ₐ[R] DualNumber A where
  toFun p := TrivSqZeroExt.inl ((p : LaurentPolynomial A).coeff 0) +
    TrivSqZeroExt.inr ((p : LaurentPolynomial A).coeff d)
  map_one' := by
    apply TrivSqZeroExt.ext
    · change (1 : LaurentPolynomial A).coeff 0 + 0 = 1
      rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
        Finsupp.single_eq_same, add_zero]
    · change 0 + (1 : LaurentPolynomial A).coeff d = 0
      rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
        Finsupp.single_eq_of_ne (show (d : ℤ) ≠ 0 by omega), zero_add]
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        add_zero, TrivSqZeroExt.fst_mul]
      exact coeff_zero_mul hd p q
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        zero_add, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
      exact coeff_degree_mul hd p q
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' p q := by
    apply TrivSqZeroExt.ext <;> simp [AddMonoidAlgebra.coeff_add]
  commutes' r := by
    apply TrivSqZeroExt.ext <;>
      simp [LaurentPolynomial.algebraMap_apply, LaurentPolynomial.C_apply,
        TrivSqZeroExt.algebraMap_eq_inl', ne_of_gt hd]

end Langlands.GroupScheme.Corepresented.GradedPrimitive

namespace Langlands.GroupScheme.Corepresented.GradedPrimitive

open CommutativeAlgebra.GradedLine

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {A : CommAlgCat.{u} R} {d : ℕ}

/-- A homogeneous algebra generator leaves no degrees between zero and its degree. -/
theorem coaction_mem_gap {c : B →+* LaurentPolynomial B} (hc : IsGrading R c)
    {x : B} (hx : x ∈ homog hc d)
    (hgen : Function.Surjective (Polynomial.aeval x : R[X] →ₐ[R] B)) (b : B) :
    c b ∈ gapAlgebra B d := by
  classical
  have hxgap : c x ∈ gapAlgebra B d := by
    intro n hn
    rw [hx, AddMonoidAlgebra.coeff_single]
    apply Finsupp.single_eq_of_ne
    intro h
    apply hn
    exact Or.inr (by omega)
  obtain ⟨p, rfl⟩ := hgen b
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add]
    exact (gapAlgebra B d).add_mem hp hq
  | monomial k r =>
    rw [Polynomial.aeval_monomial, map_mul, map_pow, hc.map_algebraMap]
    exact (gapAlgebra B d).mul_mem ((gapAlgebra B d).algebraMap_mem r)
      ((gapAlgebra B d).pow_mem hxgap k)

/-- Evaluation at an algebra generator determines every point. -/
theorem coord_generator_injective {x : B}
    (hgen : Function.Surjective (Polynomial.aeval x : R[X] →ₐ[R] B)) :
    Function.Injective fun y : F.obj A => coord e y x := by
  intro y y' h
  apply coord_injective e
  have hp : (coord e y).comp (Polynomial.aeval x) =
      (coord e y').comp (Polynomial.aeval x) := by
    apply Polynomial.algHom_ext
    simpa only [AlgHom.comp_apply, Polynomial.aeval_X] using h
  ext b
  obtain ⟨p, rfl⟩ := hgen b
  exact congrArg (fun φ : R[X] →ₐ[R] A => φ p) hp

variable (hat : F.obj A →* F.obj (CommAlgCat.of R (LaurentPolynomial A)))
  (hsupport : ∀ y b, coord e (hat y) b ∈ gapAlgebra A d)

/-- The orbit point lifted to the subalgebra supported above the first positive degree. -/
def supportedPointFun (y : F.obj A) :
    F.obj (CommAlgCat.of R (gapAlgebra A d)) :=
  ofCoord e ((coord e (hat y)).codRestrict _ (hsupport y))

theorem map_supportedPointFun (y : F.obj A) :
    F.map (subalgebraHom (A := CommAlgCat.of R (LaurentPolynomial A)) (gapAlgebra A d))
      (supportedPointFun e hat hsupport y) = hat y := by
  apply coord_injective e
  rw [coord_map, supportedPointFun, coord_ofCoord]
  exact AlgHom.val_comp_codRestrict _ _ _

/-- The supported orbit point is multiplicative. -/
def supportedPoint : F.obj A →* F.obj (CommAlgCat.of R (gapAlgebra A d)) where
  toFun := supportedPointFun e hat hsupport
  map_one' := map_subalgebraHom_injective e
    (A := CommAlgCat.of R (LaurentPolynomial A)) (gapAlgebra A d) (by
    change F.map _ (supportedPointFun e hat hsupport 1) = F.map _ 1
    rw [map_supportedPointFun, map_one, map_one])
  map_mul' y y' := map_subalgebraHom_injective e
    (A := CommAlgCat.of R (LaurentPolynomial A)) (gapAlgebra A d) (by
    change F.map _ (supportedPointFun e hat hsupport (y * y')) =
      F.map _ (supportedPointFun e hat hsupport y * supportedPointFun e hat hsupport y')
    rw [map_mul, map_supportedPointFun, map_supportedPointFun, map_supportedPointFun, map_mul])

theorem coord_supportedPoint (y : F.obj A) (b : B) :
    (coord e (supportedPoint e hat hsupport y) b : LaurentPolynomial A) =
      coord e (hat y) b := by
  change (coord e (supportedPointFun e hat hsupport y) b : LaurentPolynomial A) = _
  rw [supportedPointFun, coord_ofCoord]
  rfl

variable {hat hsupport}

/-- A homogeneous polynomial generator for a multiplicative positive grading
is an additive coordinate over an arbitrary base ring. -/
theorem coord_mul_of_homogeneous_generator {c : B →+* LaurentPolynomial B}
    (hc : IsGrading R c) (hd : 0 < d) {x : B} (hx : x ∈ homog hc d)
    (hgen : Function.Surjective (Polynomial.aeval x : R[X] →ₐ[R] B))
    (hat : F.obj A →* F.obj (CommAlgCat.of R (LaurentPolynomial A)))
    (hhat : ∀ y b, coord e (hat y) b =
      AddMonoidAlgebra.mapRingHom ℤ (coord e y).toRingHom (c b)) (y y' : F.obj A) :
    coord e (y * y') x = coord e y x + coord e y' x := by
  have hs : ∀ y b, coord e (hat y) b ∈ gapAlgebra A d := by
    intro y b n hn
    rw [hhat, AddMonoidAlgebra.coeff_mapRingHom,
      coaction_mem_gap hc hx hgen b n hn, map_zero]
  let D : CommAlgCat.of R (gapAlgebra A d) ⟶ CommAlgCat.of R (DualNumber A) :=
    CommAlgCat.ofHom (dualCoeffHom hd)
  let ζ : F.obj A →* F.obj (CommAlgCat.of R (DualNumber A)) :=
    (F.map D).hom.comp (supportedPoint e hat hs)
  have hζ : ∀ z : F.obj A, coord e (ζ z) x = TrivSqZeroExt.inr (coord e z x) := by
    intro z
    change coord e (F.map D (supportedPoint e hat hs z)) x = _
    rw [coord_map]
    change dualCoeffHom hd (coord e (supportedPoint e hat hs z) x) = _
    change TrivSqZeroExt.inl
        ((coord e (supportedPoint e hat hs z) x : LaurentPolynomial A).coeff 0) +
      TrivSqZeroExt.inr
        ((coord e (supportedPoint e hat hs z) x : LaurentPolynomial A).coeff d) = _
    rw [coord_supportedPoint, hhat, hx, AddMonoidAlgebra.mapRingHom_single,
      AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_of_ne (show (0 : ℤ) ≠ d by omega),
      Finsupp.single_eq_same, TrivSqZeroExt.inl_zero, zero_add]
    rfl
  have hunit : coord e (1 : F.obj A) x = 0 := by
    have h := congrArg TrivSqZeroExt.fst (hζ 1)
    rw [map_one, coord_one] at h
    change algebraMap R A (AffineLinearEmbedding.counit e x) = 0 at h
    rw [coord_one]
    exact h
  have hred : ∀ z : F.obj A,
      F.map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)) (ζ z) = 1 := by
    intro z
    apply coord_generator_injective e hgen
    change coord e (F.map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)) (ζ z)) x =
      coord e (1 : F.obj A) x
    rw [coord_map, AlgHom.comp_apply, hζ, hunit]
    rfl
  have key := snd_coord_mul e (hred y) (hred y') x
  rw [← map_mul] at key
  simpa only [hζ, TrivSqZeroExt.snd_inr] using key

end Langlands.GroupScheme.Corepresented.GradedPrimitive
