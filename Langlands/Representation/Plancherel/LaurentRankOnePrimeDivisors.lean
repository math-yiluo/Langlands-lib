import Langlands.Representation.Plancherel.LaurentBlockPolynomialPresentation
import Langlands.Representation.Plancherel.LaurentUnitaryCoordinatePowers
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Prime factors of Laurent polynomials in a single coordinate -/

noncomputable section

open AddMonoidAlgebra Polynomial

namespace Langlands.Plancherel

/-- Join a single first coordinate and the other coordinates into one
ordered basis chart. -/
def joinFirstLaurentCoordinate (n : ℕ) :
    ((Fin 1 → ℤ) × (Fin n → ℤ)) ≃ₗ[ℤ] (Fin (n + 1) → ℤ) where
  toFun x := Fin.cons (x.1 0) x.2
  invFun x := (fun _ => x 0, fun i => x i.succ)
  left_inv x := by
    apply Prod.ext
    · funext i
      rw [show i = 0 from Subsingleton.elim _ _]
      rfl
    · rfl
  right_inv x := by
    funext i
    cases i using Fin.cases <;> rfl
  map_add' x y := by
    funext i
    cases i using Fin.cases <;> rfl
  map_smul' c x := by
    funext i
    cases i using Fin.cases <;> rfl

@[simp]
theorem joinFirstLaurentCoordinate_first (n : ℕ) :
    joinFirstLaurentCoordinate n (Pi.single 0 1, 0) = Pi.single 0 1 := by
  funext i
  cases i using Fin.cases with
  | zero => simp [joinFirstLaurentCoordinate]
  | succ i => simp [joinFirstLaurentCoordinate]

/-- A first-coordinate root is a prime element of the full Laurent ring. -/
theorem finiteLaurentCoordinateRoot_prime (n : ℕ) (a : ℂˣ) :
    Prime (finiteLaurentCoordinateRoot n a) := by
  let b := a * Units.mk0 (2 : ℂ) (by norm_num)
  have hnz : finiteLaurentCoordinateRoot n a ≠ 0 := by
    intro h
    have he := finiteLaurentCoordinateRoot_eval_cons n a b 1
    rw [h, map_zero] at he
    have hb : (b : ℂ) - (a : ℂ) = (a : ℂ) := by simp only [b, Units.val_mul, Units.val_mk0]; ring
    exact a.ne_zero (hb.symm.trans he.symm)
  have hker : Ideal.span {finiteLaurentCoordinateRoot n a} =
      RingHom.ker (finiteLaurentFirstEvaluation n a) := by
    ext f
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, finiteLaurentCoordinateRoot_dvd_iff]
  apply (Ideal.span_singleton_prime hnz).mp
  rw [hker]
  exact RingHom.ker_isPrime _

namespace LaurentBlockInvariants

variable {n : ℕ}

local notation "First" => AddMonoidAlgebra ℂ (Fin 1 → ℤ)
local notation "Product" => AddMonoidAlgebra ℂ ((Fin 1 → ℤ) × (Fin n → ℤ))

/-- A nonzero polynomial on a rank-zero first block is a unit in the full
Laurent ring. -/
theorem isUnit_firstBlock_rank_zero (a : AddMonoidAlgebra ℂ (Fin 0 → ℤ)) (ha : a ≠ 0) :
    IsUnit (firstBlock (n := n) a) := by
  let e := AddMonoidAlgebra.uniqueRingEquiv (R := ℂ) (Fin 0 → ℤ)
  have he : firstBlock (n := n) a = algebraMap ℂ _ (e a) := by
    conv_lhs => rw [← e.symm_apply_apply a]
    simp only [e, AddMonoidAlgebra.uniqueRingEquiv_symm_apply, firstBlock_single]
    rfl
  rw [he]
  exact (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff e e.injective).mpr ha)).map (algebraMap ℂ _)

/-- The first-coordinate binomial in the product chart becomes the usual
coordinate root after adjoining the other coordinates. -/
theorem firstPolynomialMap_linearFactor (a : ℂˣ) :
    AddMonoidAlgebra.domCongr ℂ ℂ (joinFirstLaurentCoordinate n).toAddEquiv
        (firstPolynomialMap (n := n) (X - C (a : ℂ))) =
      finiteLaurentCoordinateRoot n a := by
  have hgen : (joinFirstLaurentCoordinate n).toAddEquiv (Pi.single 0 1, 0) = Pi.single 0 1 :=
    joinFirstLaurentCoordinate_first n
  apply (finiteLaurentSuccessorEquiv ℂ n).injective
  simp only [finiteLaurentCoordinateRoot, RingEquiv.apply_symm_apply, map_sub,
    firstPolynomialMap, Polynomial.aeval_X, Polynomial.aeval_C, AlgEquiv.commutes,
    AddMonoidAlgebra.domCongr_single, hgen]
  congr 1
  · simp only [finiteLaurentSuccessorEquiv, RingEquiv.trans_apply,
      AddMonoidAlgebra.mapDomainRingEquiv_single]
    change curryRingEquiv (single ((Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)).symm
      (Pi.single 0 1)) (1 : ℂ)) = _
    have hsplit : (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)).symm (Pi.single 0 1) = (1, 0) := by
      apply (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)).injective
      rw [Equiv.apply_symm_apply]
      funext i
      cases i using Fin.cases with
      | zero => simp [Fin.consEquiv]
      | succ i => simp [Fin.consEquiv]
    rw [hsplit, AddMonoidAlgebra.curryRingEquiv_single]
    rfl
  · change (finiteLaurentSuccessorEquiv ℂ n) (single 0 (a : ℂ)) = single 0 (single 0 (a : ℂ))
    simp only [finiteLaurentSuccessorEquiv, RingEquiv.trans_apply,
      AddMonoidAlgebra.mapDomainRingEquiv_single, map_zero]
    exact AddMonoidAlgebra.curryRingEquiv_single (0 : ℤ) (0 : Fin n → ℤ) (a : ℂ)

/-- A prime dividing a nonzero first-block Laurent polynomial of rank one
divides a first-coordinate binomial with nonzero complex root. -/
theorem exists_prime_dvd_firstLinearFactor (p : Product) (hp : Prime p) (a : First)
    (ha : a ≠ 0) (hpa : p ∣ firstBlock a) :
    ∃ z : ℂˣ, p ∣ firstPolynomialMap (n := n) (X - C (z : ℂ)) := by
  classical
  let ι := algebraMap Product (FractionRing Product)
  have hi : Function.Injective ι := IsFractionRing.injective _ _
  let f := ι (firstBlock (n := n) a)
  have hf : f ≠ 0 := (map_ne_zero_iff ι hi).mpr
    ((map_ne_zero_iff (firstBlock (n := n)) firstBlock_injective).mpr ha)
  have h : f = ι (firstBlock (n := n) a) / ι (firstBlock (n := n) 1) := by simp [f, ι]
  obtain ⟨P, Q, _, _, hPQ⟩ := exists_coprime_firstPolynomial_fraction _ _ f h
  have hQ : ι (firstPolynomialMap (n := n) Q) ≠ 0 := by
    intro h0
    exact hf (by rw [hPQ, h0, div_zero])
  have hP : P ≠ 0 := by
    rintro rfl
    exact hf (by simp [hPQ])
  have he : firstBlock (n := n) a * firstPolynomialMap Q = firstPolynomialMap P := hi
    (by rw [map_mul]; exact (eq_div_iff hQ).mp hPQ)
  have hd : p ∣ firstPolynomialMap P := he ▸ dvd_mul_of_dvd_left hpa _
  have hunit : IsUnit (firstPolynomialMap (n := n) (C P.leadingCoeff)) := by
    rw [firstPolynomialMap, Polynomial.aeval_C]
    exact (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP)).map (algebraMap ℂ _)
  have hprod : p ∣ (P.roots.map fun z => firstPolynomialMap (n := n) (X - C z)).prod := by
    have hpP := congrArg (firstPolynomialMap (n := n)) (IsAlgClosed.splits P).eq_prod_roots
    rw [map_mul, map_multiset_prod, Multiset.map_map] at hpP
    rw [hpP] at hd
    exact (hp.dvd_mul.mp hd).resolve_left (fun h => hp.not_isUnit (isUnit_of_dvd_unit h hunit))
  obtain ⟨g, hg, hpg⟩ := hp.exists_mem_multiset_dvd hprod
  obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hg
  have hz : z ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero, firstPolynomialMap, Polynomial.aeval_X] at hpg
    have hunit : IsUnit (single (Pi.single (0 : Fin 1) 1, 0) 1 : Product) := by
      refine isUnit_iff_exists_inv.mpr ⟨single (-Pi.single (0 : Fin 1) 1, 0) 1, ?_⟩
      rw [single_mul_single, one_mul]
      exact congrArg (fun m => single m (1 : ℂ)) (add_neg_cancel (Pi.single (0 : Fin 1) 1, 0))
    exact hp.not_isUnit (isUnit_of_dvd_unit hpg hunit)
  exact ⟨Units.mk0 z hz, hpg⟩

end LaurentBlockInvariants
end Langlands.Plancherel
