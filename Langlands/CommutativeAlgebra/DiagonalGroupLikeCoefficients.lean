import Langlands.CommutativeAlgebra.DiagonalCoalgebraImage
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Coefficients of group-like elements over arbitrary commutative rings -/

noncomputable section

universe u v w

namespace Langlands.CommutativeAlgebra.DiagonalGroupLikeCoefficients

open DiagonalCoalgebraImage

variable {R : Type u} [CommRing R] {M : Type v} [AddCommMonoid M]
  {x : AddMonoidAlgebra R M}

/-- Contracting the comultiplication in one degree isolates that coefficient. -/
theorem coeff_smul_self (hx : IsGroupLikeElem R x) (m : M) :
    x.coeff m • x = AddMonoidAlgebra.single m (x.coeff m) := by
  rw [← contract_tmul, ← hx.comul_eq_tmul_self, contract_comul]

/-- Each coefficient of a group-like element is idempotent. -/
theorem coeff_mul_self (hx : IsGroupLikeElem R x) (m : M) :
    x.coeff m * x.coeff m = x.coeff m := by
  simpa [smul_eq_mul] using
    congrArg (fun z : AddMonoidAlgebra R M => z.coeff m) (coeff_smul_self hx m)

/-- Coefficients in distinct degrees are orthogonal. -/
theorem coeff_mul_eq_zero (hx : IsGroupLikeElem R x) {m n : M} (hmn : m ≠ n) :
    x.coeff m * x.coeff n = 0 := by
  simpa [smul_eq_mul, AddMonoidAlgebra.coeff_single, Ne.symm hmn] using
    congrArg (fun z : AddMonoidAlgebra R M => z.coeff n) (coeff_smul_self hx m)

omit [AddCommMonoid M] in
/-- The diagonal counit is the finite sum of coefficients. -/
theorem counit_eq_sum_coeff (x : AddMonoidAlgebra R M) :
    Coalgebra.counit (R := R) x = x.coeff.sum (fun _ r => r) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, hx, hy, AddMonoidAlgebra.coeff_add]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  | single m r => simp

omit [AddCommMonoid M] in
/-- The orthogonal idempotent coefficients sum to one. -/
theorem sum_coeff_eq_one (hx : IsGroupLikeElem R x) :
    x.coeff.sum (fun _ r => r) = 1 := by
  rw [← counit_eq_sum_coeff, hx.counit_eq_one]

/-- The finitely supported orthogonal idempotent partition of unity defined by
the coefficients of a group-like element. -/
def coefficientPartition (x : AddMonoidAlgebra R M) (hx : IsGroupLikeElem R x) :
    {e : M →₀ R //
      (∀ m, e m * e m = e m) ∧
      (∀ m n, m ≠ n → e m * e n = 0) ∧
      e.sum (fun _ r => r) = 1} :=
  ⟨x.coeff, coeff_mul_self hx, fun _ _ h => coeff_mul_eq_zero hx h, sum_coeff_eq_one hx⟩

/-- A unit coefficient forces a group-like element to be the corresponding
degree-one monomial. -/
theorem eq_single_of_isUnit_coeff (hx : IsGroupLikeElem R x) (m : M)
    (hm : IsUnit (x.coeff m)) : x = AddMonoidAlgebra.single m 1 := by
  obtain ⟨a, ha⟩ := hm.exists_left_inv
  have h := congrArg (fun z : AddMonoidAlgebra R M => a • z) (coeff_smul_self hx m)
  simpa only [smul_smul, ha, one_smul, AddMonoidAlgebra.smul_single, smul_eq_mul] using h

/-- In any scalar extension making a coefficient invertible, the image of the
group-like element is the corresponding monomial. -/
theorem map_eq_single_of_isUnit_coeff (hx : IsGroupLikeElem R x)
    (A : Type w) [CommRing A] [Algebra R A] (m : M)
    (hm : IsUnit (algebraMap R A (x.coeff m))) :
    AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R A) x =
      AddMonoidAlgebra.single m 1 := by
  obtain ⟨a, ha⟩ := hm.exists_left_inv
  have h' :
      algebraMap R A (x.coeff m) • AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R A) x =
        AddMonoidAlgebra.single m (algebraMap R A (x.coeff m)) := by
    rw [IsScalarTower.algebraMap_smul]
    simpa using congrArg (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R A))
      (coeff_smul_self hx m)
  have h := congrArg (fun z : AddMonoidAlgebra A M => a • z) h'
  simpa only [smul_smul, ha, one_smul, AddMonoidAlgebra.smul_single, smul_eq_mul] using h

/-- Localizing at a coefficient turns a group-like element into one monomial. -/
theorem away_eq_single (hx : IsGroupLikeElem R x) (m : M) :
    AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (Localization.Away (x.coeff m))) x =
      AddMonoidAlgebra.single m 1 :=
  map_eq_single_of_isUnit_coeff hx _ m (IsLocalization.Away.algebraMap_isUnit _)

end Langlands.CommutativeAlgebra.DiagonalGroupLikeCoefficients
