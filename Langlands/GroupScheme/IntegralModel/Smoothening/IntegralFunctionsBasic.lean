import Langlands.GroupScheme.IntegralModel.IntegralFunctions
import Langlands.GroupScheme.IntegralModel.Smoothening.Saturation

/-! # Points and divisibility of integral functions

For a domain `R` with fraction field `K` and a commutative `R`-algebra `A`, the
`R`-algebra `integralFunctions R K A` contains the image of `A`, every `R`-point of
`A` extends uniquely to it, and an integral function all of whose values are
divisible by `s` is `s` times an integral function. -/

noncomputable section

universe u v

open scoped TensorProduct

namespace Langlands.GroupScheme.IntegralModel.Smoothening

variable {R : Type u} {K : Type u} [CommRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Type v} [CommRing A] [Algebra R A]

omit [IsFractionRing R K] in
variable (R K A) in
/-- The functions `1 ⊗ a` are integral. -/
theorem one_tmul_mem_integralFunctions (a : A) :
    (1 : K) ⊗ₜ[R] a ∈ integralFunctions R K A := by
  rw [mem_integralFunctions]
  intro φ
  exact ⟨φ a, by simp⟩

variable (R K A) in
/-- The inclusion of `A` into its integral functions. -/
def incl : A →ₐ[R] integralFunctions R K A :=
  (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).codRestrict _
    (one_tmul_mem_integralFunctions R K A)

omit [IsFractionRing R K] in
@[simp]
theorem coe_incl (a : A) : (incl R K A a : K ⊗[R] A) = (1 : K) ⊗ₜ a :=
  rfl

/-- The generic fibre is a torsion-free `R`-module. -/
instance isTorsionFree_tensor [IsDomain R] : Module.IsTorsionFree R (K ⊗[R] A) where
  isSMulRegular _ hr _ _ h := smul_left_cancel K A hr.ne_zero h

instance isTorsionFree_integralFunctions [IsDomain R] :
    Module.IsTorsionFree R (integralFunctions R K A) :=
  Subtype.val_injective.moduleIsTorsionFree _ fun _ _ => rfl

theorem incl_injective [Module.Flat R A] :
    Function.Injective (incl R K A) := fun _ _ h =>
  includeRight_injective_of_flat (R := R) K A (congrArg Subtype.val h)

omit [IsFractionRing R K] in
theorem genericEval_mem_bot (φ : A →ₐ[R] R) (b : integralFunctions R K A) :
    genericEval R K A φ b ∈ (⊥ : Subalgebra R K) :=
  Algebra.mem_bot.2 ((mem_integralFunctions R K A).1 b.2 φ)

/-- The extension of an `R`-point of `A` to the integral functions. -/
def point (φ : A →ₐ[R] R) : integralFunctions R K A →ₐ[R] R :=
  (Algebra.botEquivOfInjective (IsFractionRing.injective R K)).toAlgHom.comp
    ((((genericEval R K A φ).restrictScalars R).comp (integralFunctions R K A).val).codRestrict
      ⊥ (genericEval_mem_bot φ))

theorem algebraMap_point (φ : A →ₐ[R] R) (b : integralFunctions R K A) :
    algebraMap R K (point φ b) = genericEval R K A φ b := by
  set e := Algebra.botEquivOfInjective (IsFractionRing.injective R K)
  set x : (⊥ : Subalgebra R K) := ⟨genericEval R K A φ b, genericEval_mem_bot φ b⟩
  have h : e.symm (e x) = x := e.symm_apply_apply x
  exact congrArg Subtype.val h

theorem point_incl (φ : A →ₐ[R] R) (a : A) : point (K := K) φ (incl R K A a) = φ a := by
  apply IsFractionRing.injective R K
  rw [algebraMap_point, coe_incl, genericEval_tmul, one_mul]

theorem point_comp_incl (φ : A →ₐ[R] R) : (point (K := K) φ).comp (incl R K A) = φ :=
  AlgHom.ext (point_incl φ)

/-- Every `R`-point of the integral functions is the extension of its restriction to
`A`. -/
theorem eq_point [IsDomain R] (ψ : integralFunctions R K A →ₐ[R] R) :
    ψ = point (ψ.comp (incl R K A)) := by
  refine algHom_ext (D := R) _ _ _ fun a ha => ?_
  have h : (⟨_, ha⟩ : integralFunctions R K A) = incl R K A a := rfl
  rw [h, point_incl]
  rfl

/-- An integral function whose values at all `R`-points are divisible by `s ≠ 0` is
`s` times an integral function. -/
theorem exists_eq_smul_of_dvd {s : R} (hs : s ≠ 0) (b : integralFunctions R K A)
    (h : ∀ φ : A →ₐ[R] R, s ∣ point φ b) :
    ∃ b' : integralFunctions R K A, b = s • b' := by
  have hs' : algebraMap R K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hs
  have hmem : (algebraMap R K s)⁻¹ • (b : K ⊗[R] A) ∈ integralFunctions R K A := by
    rw [mem_integralFunctions]
    intro φ
    obtain ⟨t, ht⟩ := h φ
    refine ⟨t, ?_⟩
    rw [map_smul, ← algebraMap_point, ht, map_mul, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hs', one_mul]
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  change (b : K ⊗[R] A) = s • ((algebraMap R K s)⁻¹ • (b : K ⊗[R] A))
  rw [← algebraMap_smul K s, smul_smul, mul_inv_cancel₀ hs', one_smul]

/-- Values of a scalar multiple. -/
theorem point_smul (φ : A →ₐ[R] R) (s : R) (b : integralFunctions R K A) :
    point (K := K) φ (s • b) = s * point φ b := by
  rw [map_smul, smul_eq_mul]

end Langlands.GroupScheme.IntegralModel.Smoothening
