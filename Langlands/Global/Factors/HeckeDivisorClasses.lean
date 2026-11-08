import Langlands.Global.Factors.HeckeDivisor
import Mathlib.NumberTheory.NumberField.ClassNumber

/-! # Principal generators and ideal-class representatives of finite Hecke divisors -/

noncomputable section

universe u

namespace Langlands.Global.HeckeDivisor

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.ClassField.Global
open scoped NumberField nonZeroDivisors

variable {K : Type u} [Field K] [NumberField K]

@[simp] theorem principalDivisor_inv (a : Kˣ) :
    principalDivisor a⁻¹ = -principalDivisor a := by
  rw [eq_neg_iff_add_eq_zero, ← principalDivisor_mul, inv_mul_cancel, principalDivisor_one]

/-- Global integral units have zero principal divisor. -/
@[simp] theorem principalDivisor_units_map (u : (𝓞 K)ˣ) :
    principalDivisor (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u) = 0 :=
  (principalDivisor_eq_zero_iff _).mpr ⟨u, rfl⟩

/-- The inclusion of global integral units into the nonzero field elements is injective. -/
theorem units_map_injective :
    Function.Injective (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K)) := by
  intro u w h
  apply Units.ext
  apply IsFractionRing.injective (𝓞 K) K
  simpa only [Units.coe_map, MonoidHom.coe_coe] using congrArg Units.val h

variable (K) in
/-- The additive subgroup of principal finite divisors. -/
def principalDivisors : AddSubgroup (FinitePlaceDivisor K) where
  carrier := Set.range principalDivisor
  zero_mem' := ⟨1, principalDivisor_one⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, principalDivisor_mul a b⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a⁻¹, principalDivisor_inv a⟩

theorem mem_principalDivisors (d : FinitePlaceDivisor K) :
    d ∈ principalDivisors K ↔ ∃ a : Kˣ, principalDivisor a = d := Iff.rfl

theorem principalDivisor_mem (a : Kˣ) : principalDivisor a ∈ principalDivisors K :=
  ⟨a, rfl⟩

/-- A chosen generator of a principal finite divisor. -/
def principalGenerator (p : principalDivisors K) : Kˣ :=
  Classical.choose p.property

@[simp] theorem principalDivisor_principalGenerator (p : principalDivisors K) :
    principalDivisor (principalGenerator p) = p :=
  Classical.choose_spec p.property

/-- Principal divisors and integral units parametrize the nonzero elements of the field. -/
def principalUnitsEquiv : principalDivisors K × (𝓞 K)ˣ ≃ Kˣ :=
  Equiv.ofBijective
    (fun x => Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) x.2 * principalGenerator x.1)
    ⟨by
      rintro ⟨p, u⟩ ⟨q, w⟩ h
      dsimp only at h
      have hpq : p = q := by
        apply Subtype.ext
        simpa only [principalDivisor_mul, principalDivisor_units_map, zero_add,
          principalDivisor_principalGenerator] using congrArg principalDivisor h
      subst hpq
      exact Prod.ext rfl (units_map_injective (mul_right_cancel h)),
    by
      intro a
      let p : principalDivisors K := ⟨principalDivisor a, principalDivisor_mem a⟩
      obtain ⟨u, hu⟩ := (principalDivisor_eq_zero_iff (a * (principalGenerator p)⁻¹)).mp (by
        rw [principalDivisor_mul, principalDivisor_inv, principalDivisor_principalGenerator]
        exact add_neg_cancel _)
      refine ⟨(p, u), ?_⟩
      dsimp only
      rw [hu, inv_mul_cancel_right]⟩

@[simp] theorem principalUnitsEquiv_apply (p : principalDivisors K) (u : (𝓞 K)ˣ) :
    principalUnitsEquiv (p, u) =
      Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u * principalGenerator p :=
  rfl

/-- The principal-divisor coordinate of the parametrization is the principal divisor. -/
theorem principalDivisor_principalUnitsEquiv (x : principalDivisors K × (𝓞 K)ˣ) :
    principalDivisor (principalUnitsEquiv x) = x.1 := by
  obtain ⟨p, u⟩ := x
  rw [principalUnitsEquiv_apply, principalDivisor_mul, principalDivisor_units_map, zero_add,
    principalDivisor_principalGenerator]

@[simp] theorem principalUnitsEquiv_symm_apply_fst (a : Kˣ) :
    ((principalUnitsEquiv.symm a).1 : FinitePlaceDivisor K) = principalDivisor a := by
  conv_rhs => rw [← principalUnitsEquiv.apply_symm_apply a]
  rw [principalDivisor_principalUnitsEquiv]

/-- The actual ideal class of the prime-product fractional ideal of a finite divisor. -/
def divisorClass (d : FinitePlaceDivisor K) : ClassGroup (𝓞 K) :=
  ClassGroup.mk K (finiteDivisorFractionalIdeal K d)

@[simp] theorem divisorClass_zero : divisorClass (0 : FinitePlaceDivisor K) = 1 := by
  rw [divisorClass, finiteDivisorFractionalIdeal_zero, map_one]

@[simp] theorem divisorClass_add (d e : FinitePlaceDivisor K) :
    divisorClass (d + e) = divisorClass d * divisorClass e := by
  rw [divisorClass, finiteDivisorFractionalIdeal_add, map_mul]
  rfl

@[simp] theorem divisorClass_neg (d : FinitePlaceDivisor K) :
    divisorClass (-d) = (divisorClass d)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← divisorClass_add, neg_add_cancel, divisorClass_zero]

@[simp] theorem divisorClass_sub (d e : FinitePlaceDivisor K) :
    divisorClass (d - e) = divisorClass d / divisorClass e := by
  rw [sub_eq_add_neg, divisorClass_add, divisorClass_neg, div_eq_mul_inv]

/-- Every actual ideal class contains the prime-product ideal of a finite divisor. -/
theorem divisorClass_surjective : Function.Surjective (divisorClass (K := K)) := by
  intro C
  exact ClassGroup.induction K (P := fun C => ∃ d : FinitePlaceDivisor K, divisorClass d = C)
    (fun I => ⟨fractionalIdealDivisor K I, by
      rw [divisorClass, finiteDivisorFractionalIdeal_fractionalIdealDivisor]⟩) C

/-- The kernel of the divisor class map is exactly the principal divisor subgroup. -/
theorem divisorClass_eq_one_iff (d : FinitePlaceDivisor K) :
    divisorClass d = 1 ↔ d ∈ principalDivisors K := by
  rw [divisorClass, ← (ClassGroup.equiv K).injective.eq_iff, ClassGroup.equiv_mk, map_one,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, MonoidHom.mem_range]
  have hrefl (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      Units.mapEquiv (MulEquiv.refl (FractionalIdeal (𝓞 K)⁰ K)) I = I :=
    Units.ext rfl
  simp only [FractionalIdeal.canonicalEquiv_self, RingEquiv.coe_mulEquiv_refl, hrefl]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← fractionalIdealDivisor_finiteDivisorFractionalIdeal K (principalDivisor a),
      fractionalIdeal_principalDivisor, ha, fractionalIdealDivisor_finiteDivisorFractionalIdeal]
  · rintro ⟨a, rfl⟩
    exact ⟨a, (fractionalIdeal_principalDivisor a).symm⟩

theorem divisorClass_eq_one_of_mem {d : FinitePlaceDivisor K} (hd : d ∈ principalDivisors K) :
    divisorClass d = 1 :=
  (divisorClass_eq_one_iff d).mpr hd

@[simp] theorem divisorClass_principalDivisor (a : Kˣ) : divisorClass (principalDivisor a) = 1 :=
  divisorClass_eq_one_of_mem (principalDivisor_mem a)

/-- Two finite divisors are in the same actual ideal class exactly when they differ principally. -/
theorem sub_mem_principalDivisors_iff (d e : FinitePlaceDivisor K) :
    d - e ∈ principalDivisors K ↔ divisorClass d = divisorClass e := by
  rw [← divisorClass_eq_one_iff, divisorClass_sub, div_eq_one]

/-- A chosen finite divisor representing each actual ideal class. -/
def classRepresentative (C : ClassGroup (𝓞 K)) : FinitePlaceDivisor K :=
  Classical.choose (divisorClass_surjective C)

@[simp] theorem divisorClass_classRepresentative (C : ClassGroup (𝓞 K)) :
    divisorClass (classRepresentative C) = C :=
  Classical.choose_spec (divisorClass_surjective C)

/-- Every finite divisor is uniquely a principal divisor plus a chosen class representative. -/
def classPrincipalEquiv : ClassGroup (𝓞 K) × principalDivisors K ≃ FinitePlaceDivisor K :=
  Equiv.ofBijective (fun x => (x.2 : FinitePlaceDivisor K) + classRepresentative x.1)
    ⟨by
      rintro ⟨C, p⟩ ⟨D, q⟩ h
      dsimp only at h
      have hCD : C = D := by
        simpa only [divisorClass_add, divisorClass_eq_one_of_mem p.2,
          divisorClass_eq_one_of_mem q.2, one_mul, divisorClass_classRepresentative] using
          congrArg divisorClass h
      subst hCD
      exact Prod.ext rfl (Subtype.ext (add_right_cancel h)),
    by
      intro d
      refine ⟨(divisorClass d, ⟨d - classRepresentative (divisorClass d), ?_⟩), ?_⟩
      · rw [sub_mem_principalDivisors_iff, divisorClass_classRepresentative]
      · exact sub_add_cancel _ _⟩

@[simp] theorem classPrincipalEquiv_apply (C : ClassGroup (𝓞 K)) (p : principalDivisors K) :
    classPrincipalEquiv (C, p) = (p : FinitePlaceDivisor K) + classRepresentative C :=
  rfl

/-- Every finite divisor is uniquely a principal divisor minus a chosen class representative. -/
def classPrincipalNegEquiv : ClassGroup (𝓞 K) × principalDivisors K ≃ FinitePlaceDivisor K :=
  Equiv.ofBijective (fun x => (x.2 : FinitePlaceDivisor K) - classRepresentative x.1)
    ⟨by
      rintro ⟨C, p⟩ ⟨D, q⟩ h
      dsimp only at h
      have hCD : C⁻¹ = D⁻¹ := by
        simpa only [divisorClass_sub, divisorClass_eq_one_of_mem p.2,
          divisorClass_eq_one_of_mem q.2, one_div, divisorClass_classRepresentative] using
          congrArg divisorClass h
      rw [inv_inj] at hCD
      subst hCD
      exact Prod.ext rfl (Subtype.ext (sub_left_inj.mp h)),
    by
      intro d
      refine ⟨((divisorClass d)⁻¹,
        ⟨d + classRepresentative (divisorClass d)⁻¹, ?_⟩), ?_⟩
      · rw [← divisorClass_eq_one_iff, divisorClass_add, divisorClass_classRepresentative,
          mul_inv_cancel]
      · exact add_sub_cancel_right _ _⟩

@[simp] theorem classPrincipalNegEquiv_apply (C : ClassGroup (𝓞 K)) (p : principalDivisors K) :
    classPrincipalNegEquiv (C, p) = (p : FinitePlaceDivisor K) - classRepresentative C :=
  rfl

end Langlands.Global.HeckeDivisor
