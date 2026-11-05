import Langlands.GroupScheme.Rational.LaurentFrobeniusBasis
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Additive-polynomial coordinates of pointed Laurent functions -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.LaurentAugmentation

open MvPolynomial

variable {p : ℕ} [hp : Fact p.Prime] {I : Type v}

/-- The additive-polynomial exponent corresponding to a Frobenius-orbit index. -/
def orbitExponent (x : {m : I → ℤ // IsPrimitive p m} × ℕ) :
    {m : I → ℤ // IsPrimitive p m} →₀ ℕ :=
  Finsupp.single x.1 (p ^ x.2)

theorem orbitExponent_injective :
    Function.Injective (orbitExponent (p := p) (I := I)) := by
  classical
  rintro ⟨a, r⟩ ⟨b, s⟩ h
  have hab : a = b := by
    by_contra hne
    have h' := congrArg (fun d => d a) h
    have hz : p ^ r = 0 := by
      simpa only [orbitExponent, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne hne] using h'
    exact (pow_ne_zero _ hp.out.ne_zero) hz
  subst b
  have hrs : p ^ r = p ^ s := by
    simpa [orbitExponent] using congrArg (fun d => d a) h
  exact Prod.ext rfl (Nat.pow_right_injective hp.out.two_le hrs)

variable (k : Type u) [CommRing k] (p) (I)

/-- Encode a pointed Laurent function by sending the coefficient basis vector
`X^((p^r) • m) - 1` to `Y_m^(p^r)`. In characteristic `p`, the input
also equals `(X^m - 1)^(p^r)`. -/
def additiveEncoding :
    space k (I → ℤ) →ₗ[k] MvPolynomial {m : I → ℤ // IsPrimitive p m} k :=
  ((basisMonomials {m : I → ℤ // IsPrimitive p m} k).repr.symm.toLinearMap).comp
    ((Finsupp.lmapDomain k k orbitExponent).comp
      (frobeniusBasis k p I).repr.toLinearMap)

theorem additiveEncoding_injective :
    Function.Injective (additiveEncoding (k := k) (p := p) (I := I)) :=
  (basisMonomials {m : I → ℤ // IsPrimitive p m} k).repr.symm.injective.comp
    ((Finsupp.mapDomain_injective orbitExponent_injective).comp
      (frobeniusBasis k p I).repr.injective)

@[simp] theorem additiveEncoding_basis (a : {m : I → ℤ // IsPrimitive p m}) (r : ℕ) :
    additiveEncoding (k := k) (p := p) (I := I) (frobeniusBasis k p I (a, r)) = X a ^ p ^ r := by
  simp [additiveEncoding, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    orbitExponent, ← X_pow_eq_monomial]

section Frobenius

variable [CharP k p]

/-- Frobenius as a semilinear endomorphism of the augmentation kernel. -/
def frobeniusMap : space k (I → ℤ) →ₛₗ[_root_.frobenius k p] space k (I → ℤ) where
  toFun f := ⟨f.val ^ p, by
    simpa using pow_mem_space p f.property 1⟩
  map_add' f g := by
    apply Subtype.ext
    change (f.val + g.val) ^ p = f.val ^ p + g.val ^ p
    have : CharP (AddMonoidAlgebra k (I → ℤ)) p :=
      charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k _) p
    exact add_pow_char _ _ _
  map_smul' c f := by
    apply Subtype.ext
    exact smul_pow c f.val p

@[simp] theorem frobeniusMap_val (f : space k (I → ℤ)) :
    (frobeniusMap (k := k) (p := p) (I := I) f).val = f.val ^ p := rfl

@[simp] theorem frobeniusMap_basis (a : {m : I → ℤ // IsPrimitive p m}) (r : ℕ) :
    frobeniusMap (k := k) (p := p) (I := I) (frobeniusBasis k p I (a, r)) =
      frobeniusBasis k p I (a, r + 1) := by
  apply Subtype.ext
  rw [frobeniusMap_val, frobeniusBasis_apply, frobeniusBasis_apply, pow_succ, pow_mul]

theorem additiveEncoding_frobenius (f : space k (I → ℤ)) :
    additiveEncoding (k := k) (p := p) (I := I) (frobeniusMap (k := k) (p := p) (I := I) f) =
      additiveEncoding (k := k) (p := p) (I := I) f ^ p := by
  have h : (additiveEncoding (k := k) (p := p) (I := I)).comp (frobeniusMap (k := k) (p := p) (I := I)) =
      (LinearMap.frobenius k (MvPolynomial {m : I → ℤ // IsPrimitive p m} k) p).comp
        (additiveEncoding (k := k) (p := p) (I := I)) := by
    apply (frobeniusBasis k p I).ext
    rintro ⟨a, r⟩
    simp only [LinearMap.comp_apply, frobeniusMap_basis, additiveEncoding_basis,
      LinearMap.frobenius_def, pow_succ, pow_mul]
  exact DFunLike.congr_fun h f

end Frobenius

end Langlands.GroupScheme.LaurentAugmentation
