import Langlands.Global.Arithmetic.CharacterPrescriptionStatement
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Finite quotients for local character prescription

The local domain includes the whole infinite idele factor. The statement at
the end is an arithmetic existence assertion, not an assumption or instance.
-/

noncomputable section

universe u

namespace Langlands.Global

open scoped Classical

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))

/-- The product of all infinite factors and the selected actual finite factors. -/
abbrev PrescriptionLocalProduct :=
  (InfiniteAdeles K)ˣ × ((v : {v // v ∈ S}) → (FiniteCompletion K v.1)ˣ)

/-- Insert the selected factors into the actual full idele group. -/
def prescriptionIdeleInclusion : PrescriptionLocalProduct K S →ₜ* Ideles K := by
  classical
  exact
    { toFun := fun a =>
        infiniteIdelesInclusion K a.1 *
          ∏ v, finiteIdeleInclusion K v.1 (a.2 v)
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, map_mul,
          Finset.prod_mul_distrib]
        ac_rfl
      continuous_toFun :=
        ((infiniteIdelesInclusion K).continuous.comp continuous_fst).mul
          (continuous_finsetProd _ fun v _ =>
            (finiteIdeleInclusion K v.1).continuous.comp
              ((continuous_apply v).comp continuous_snd)) }

/-- The same actual local product mapped to the idele-class quotient. -/
def prescriptionClassMap : PrescriptionLocalProduct K S →ₜ* IdeleClasses K :=
  (ideleClassMap K).comp (prescriptionIdeleInclusion K S)

/-- Multiply the given local characters, including the whole infinite character. -/
def prescriptionLocalCharacter
    (η : (v : {v // v ∈ S}) → (FiniteCompletion K v.1)ˣ →ₜ* ℂˣ)
    (ηInf : (InfiniteAdeles K)ˣ →ₜ* ℂˣ) :
    PrescriptionLocalProduct K S →ₜ* ℂˣ := by
  classical
  exact
    { toFun := fun a => ηInf a.1 * ∏ v, η v (a.2 v)
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, map_mul,
          Finset.prod_mul_distrib]
        ac_rfl
      continuous_toFun :=
        (ηInf.continuous.comp continuous_fst).mul
          (continuous_finsetProd _ fun v _ =>
            (η v).continuous.comp ((continuous_apply v).comp continuous_snd)) }

@[simp]
theorem prescriptionIdeleInclusion_infinity (a : (InfiniteAdeles K)ˣ) :
    prescriptionIdeleInclusion K S (a, 1) = infiniteIdelesInclusion K a := by
  classical
  change infiniteIdelesInclusion K a *
    ∏ v : {v // v ∈ S}, finiteIdeleInclusion K v.1 1 = _
  simp

@[simp]
theorem prescriptionIdeleInclusion_finite
    (v : {v // v ∈ S}) (a : (FiniteCompletion K v.1)ˣ) :
    prescriptionIdeleInclusion K S (1, Pi.mulSingle v a) =
      finiteIdeleInclusion K v.1 a := by
  classical
  change infiniteIdelesInclusion K 1 *
    ∏ w : {v // v ∈ S}, finiteIdeleInclusion K w.1
      (Pi.mulSingle (M := fun w : {v // v ∈ S} => (FiniteCompletion K w.1)ˣ) v a w) = _
  simp only [map_one, one_mul]
  rw [Finset.prod_eq_single v]
  · simp
  · intro w _ hw
    simp [Pi.mulSingle_eq_of_ne hw]
  · simp

@[simp]
theorem prescriptionClassMap_infinity (a : (InfiniteAdeles K)ˣ) :
    prescriptionClassMap K S (a, 1) =
      ideleClassMap K (infiniteIdelesInclusion K a) := by
  simp [prescriptionClassMap]

@[simp]
theorem prescriptionClassMap_finite
    (v : {v // v ∈ S}) (a : (FiniteCompletion K v.1)ˣ) :
    prescriptionClassMap K S (1, Pi.mulSingle v a) = finiteClassInclusion K v.1 a := by
  simp [prescriptionClassMap, finiteClassInclusion]

@[simp]
theorem prescriptionLocalCharacter_infinity
    (η : (v : {v // v ∈ S}) → (FiniteCompletion K v.1)ˣ →ₜ* ℂˣ)
    (ηInf : (InfiniteAdeles K)ˣ →ₜ* ℂˣ) (a : (InfiniteAdeles K)ˣ) :
    prescriptionLocalCharacter K S η ηInf (a, 1) = ηInf a := by
  classical
  change ηInf a * ∏ v : {v // v ∈ S}, η v 1 = _
  simp

@[simp]
theorem prescriptionLocalCharacter_finite
    (η : (v : {v // v ∈ S}) → (FiniteCompletion K v.1)ˣ →ₜ* ℂˣ)
    (ηInf : (InfiniteAdeles K)ˣ →ₜ* ℂˣ)
    (v : {v // v ∈ S}) (a : (FiniteCompletion K v.1)ˣ) :
    prescriptionLocalCharacter K S η ηInf (1, Pi.mulSingle v a) = η v a := by
  classical
  change ηInf 1 * ∏ w : {v // v ∈ S}, η w
    (Pi.mulSingle (M := fun w : {v // v ∈ S} => (FiniteCompletion K w.1)ˣ) v a w) = _
  simp only [map_one, one_mul]
  rw [Finset.prod_eq_single v]
  · simp
  · intro w _ hw
    simp [Pi.mulSingle_eq_of_ne hw]
  · simp

/-- The period-doubling part of Artin--Tate X.2 Theorem 4, on the actual
local product and idele classes. The preimage is an equality of subgroups. -/
def PrescriptionFiniteQuotientStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (n : ℕ), 0 < n →
    ∀ U : OpenSubgroup (PrescriptionLocalProduct K S),
      U.toSubgroup.FiniteIndex →
      (∀ a : PrescriptionLocalProduct K S, a ^ n ∈ U) →
      ∃ N : OpenSubgroup (IdeleClasses K),
        N.toSubgroup.FiniteIndex ∧
        (∀ c : IdeleClasses K, c ^ (2 * n) ∈ N) ∧
        N.toSubgroup.comap (prescriptionClassMap K S).toMonoidHom = U.toSubgroup

end Langlands.Global
