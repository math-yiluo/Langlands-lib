import Langlands.Geometry.FormalGroup.DrinfeldCyclicBasis

/-! # Extending the cyclic generators to an action of the actual division order -/

noncomputable section

open scoped BigOperators

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision

universe u s

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)
variable {π : 𝒪[K]} (uniformizer : Dˣ) (σ : L ≃ₐ[K] L)

local notation "d" => CentralSimple.reducedDegree K D
local notation "C" => SubfieldIntegerRing K D ι

private theorem reduce_cyclic_pow {A : Type*} [Monoid A] (p a : A) (n degree : ℕ)
    (hp : p ^ degree = a) :
    p ^ n = a ^ (n / degree) * p ^ (n % degree) := by
  calc
    p ^ n = p ^ (degree * (n / degree) + n % degree) := by rw [Nat.div_add_mod]
    _ = a ^ (n / degree) * p ^ (n % degree) := by rw [pow_add, pow_mul, hp]

private theorem cyclic_monomial_mul {A : Type*} [Ring A]
    (ρ : C →+* A) (p : A) (f : C → C) (hf : ∀ a, p * ρ a = ρ (f a) * p)
    (a b : C) (m n : ℕ) :
    (ρ a * p ^ m) * (ρ b * p ^ n) = ρ (a * f^[m] b) * p ^ (m + n) := by
  have hpow (k : ℕ) : p ^ k * ρ b = ρ (f^[k] b) * p ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_assoc, ih, ← mul_assoc, hf, mul_assoc, Function.iterate_succ_apply']
  calc
    (ρ a * p ^ m) * (ρ b * p ^ n) = ρ a * ((p ^ m * ρ b) * p ^ n) := by
      simp only [mul_assoc]
    _ = ρ (a * f^[m] b) * p ^ (m + n) := by rw [hpow, map_mul, pow_add]; simp only [mul_assoc]

/-- A coefficient homomorphism and an operator satisfying the cyclic relations extend to the
actual division order. The extension is unique by `drinfeldOrder_ringHom_ext`. -/
def drinfeldCyclicOrderLift (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (hπ : Irreducible π)
    (hUniformizer : (uniformizer : D) ^ d = algebraMap K D (π : K))
    (hMul : ∀ a : L, (uniformizer : D) * ι a = ι (σ a) * (uniformizer : D))
    {A : Type*} [Ring A] (ρ : C →+* A) (p : A)
    (hp : p ^ d = ρ (algebraMap 𝒪[K] C π))
    (hComm : ∀ a : C, p * ρ a = ρ (subfieldIntegerFrobenius ι σ hL a) * p) :
    {g : IntegerRing K D →+* A //
      (∀ a : C, g (subfieldIntegerInclusion K D ι a) = ρ a) ∧
        g (drinfeldIntegralUniformizer uniformizer hUniformizer) = p} := by
  let e := drinfeldIntegralCyclicEquiv ι uniformizer hL hπ hUniformizer
  let P := drinfeldIntegralUniformizer uniformizer hUniformizer
  let inc := (subfieldIntegerInclusion K D ι).toRingHom
  let f := subfieldIntegerFrobenius ι σ hL
  let eval : (Fin d → C) →+ A :=
    { toFun := fun c => ∑ i, ρ (c i) * p ^ i.val
      map_zero' := by simp
      map_add' := fun a b => by
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib] }
  let extend := eval.comp e.symm.toAddEquiv.toAddMonoidHom
  have he (a : Fin d → C) : e a = ∑ i, inc (a i) * P ^ i.val :=
    drinfeldIntegralCyclicEquiv_apply ι uniformizer hL hπ hUniformizer a
  have e_single (i : Fin d) (a : C) : e (Pi.single i a) = inc a * P ^ i.val := by
    rw [he, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  have extend_single (i : Fin d) (a : C) :
      extend (inc a * P ^ i.val) = ρ a * p ^ i.val := by
    rw [← e_single]
    change (∑ j, ρ (e.symm (e (Pi.single i a)) j) * p ^ j.val) = _
    rw [e.symm_apply_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  have hP : P ^ d = inc (algebraMap 𝒪[K] C π) :=
    (drinfeldIntegralUniformizer_pow uniformizer hUniformizer).trans
      ((subfieldIntegerInclusion K D ι).commutes π).symm
  have extend_monomial (a : C) (n : ℕ) : extend (inc a * P ^ n) = ρ a * p ^ n := by
    let i : Fin d := ⟨n % d, Nat.mod_lt _ (CentralSimple.reducedDegree_pos K D)⟩
    rw [reduce_cyclic_pow P _ n d hP, reduce_cyclic_pow p _ n d hp,
      ← mul_assoc, ← mul_assoc, ← map_pow inc, ← map_pow ρ, ← map_mul inc, ← map_mul ρ]
    exact extend_single i (a * (algebraMap 𝒪[K] C π) ^ (n / d))
  have extend_mul_monomial (a b : C) (m n : ℕ) :
      extend ((inc a * P ^ m) * (inc b * P ^ n)) =
        extend (inc a * P ^ m) * extend (inc b * P ^ n) := by
    have hInt := drinfeldIntegralUniformizer_mul_subfield ι uniformizer σ hUniformizer hMul hL
    rw [cyclic_monomial_mul ι inc P f hInt a b m n, extend_monomial,
      extend_monomial, extend_monomial, cyclic_monomial_mul ι ρ p f hComm a b m n]
  have extend_mul (a b : IntegerRing K D) : extend (a * b) = extend a * extend b := by
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    simp only [he, Finset.sum_mul, Finset.mul_sum, map_sum, extend_mul_monomial]
  let g : IntegerRing K D →+* A :=
    { __ := extend
      map_one' := by simpa using extend_monomial 1 0
      map_mul' := extend_mul }
  refine ⟨g, ?_, ?_⟩
  · intro a
    change extend (inc a) = ρ a
    simpa using extend_monomial a 0
  · change extend P = p
    simpa using extend_monomial 1 1

end Langlands.FormalGroup.LocalDivision
