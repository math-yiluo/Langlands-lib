import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Skew elements and quadratic coordinates -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.SU3Root

universe u v

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

local instance quadraticDataFiniteDimensional : FiniteDimensional F E :=
  .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]; decide)

/-- An element is fixed by the conjugation exactly when it comes from the base field. -/
theorem conjugation_eq_self_iff (x : E) :
    conjugation F E x = x ↔ x ∈ Set.range (algebraMap F E) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  constructor
  · intro h f
    by_cases hf : f = 1
    · subst hf; rfl
    · rw [conjugation_unique F E f hf]; exact h
  · intro h
    exact h _

omit [Algebra.IsSeparable F E] in
theorem exists_not_mem_range : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
  by_contra! h
  have htop : (⊥ : Subalgebra F E) = ⊤ := Algebra.eq_top_iff.mpr fun x => by
    obtain ⟨y, rfl⟩ := h x
    exact Subalgebra.algebraMap_mem _ y
  have : Module.finrank F E = 1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop
  rw [Algebra.IsQuadraticExtension.finrank_eq_two F E] at this
  exact absurd this (by decide)

variable [CharZero F]

omit [CharZero F] in
/-- A nonzero element negated by the conjugation. -/
theorem exists_skew : ∃ r : E, r ≠ 0 ∧ conjugation F E r = -r := by
  obtain ⟨x, hx⟩ := exists_not_mem_range F E
  refine ⟨x - conjugation F E x, fun h => hx ?_, ?_⟩
  · exact (conjugation_eq_self_iff F E x).mp (sub_eq_zero.mp h).symm
  · rw [map_sub, conjugation_involutive F E x, neg_sub]

/-- A chosen nonzero element `r` with `σ r = -r`. In characteristic zero it generates
`E` over `F`. -/
def skewRoot : E := Classical.choose (exists_skew F E)

omit [CharZero F] in
theorem skewRoot_ne_zero : skewRoot F E ≠ 0 := (Classical.choose_spec (exists_skew F E)).1

omit [CharZero F] in
theorem conjugation_skewRoot : conjugation F E (skewRoot F E) = -skewRoot F E :=
  (Classical.choose_spec (exists_skew F E)).2

theorem skewRoot_sq_mem : skewRoot F E * skewRoot F E ∈ Set.range (algebraMap F E) := by
  rw [← conjugation_eq_self_iff, map_mul, conjugation_skewRoot, neg_mul_neg]

/-- The square `d = r²`, an element of the base field. -/
def skewSq : F := Classical.choose (skewRoot_sq_mem F E)

theorem algebraMap_skewSq : algebraMap F E (skewSq F E) = skewRoot F E * skewRoot F E :=
  Classical.choose_spec (skewRoot_sq_mem F E)

theorem skewRoot_not_mem_range : skewRoot F E ∉ Set.range (algebraMap F E) := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  intro h
  have h1 := (conjugation_eq_self_iff F E _).mpr h
  rw [conjugation_skewRoot, neg_eq_iff_add_eq_zero, ← two_mul] at h1
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  exact skewRoot_ne_zero F E ((mul_eq_zero.mp h1).resolve_left h2)

theorem not_isSquare_skewSq : ¬ IsSquare (skewSq F E) := by
  rintro ⟨s, hs⟩
  have : (skewRoot F E - algebraMap F E s) * (skewRoot F E + algebraMap F E s) = 0 := by
    have := algebraMap_skewSq F E
    rw [hs, map_mul] at this
    linear_combination -this
  rcases mul_eq_zero.mp this with h | h
  · exact skewRoot_not_mem_range F E ⟨s, (sub_eq_zero.mp h).symm⟩
  · exact skewRoot_not_mem_range F E ⟨-s, by rw [map_neg]; exact (neg_eq_of_add_eq_zero_left h)⟩

local instance : Fact (¬ IsSquare (skewSq F E)) := ⟨not_isSquare_skewSq F E⟩

/-- The algebra map `F(√d) → E`, sending `ω` to the skew root. -/
def skewLift : QuadraticAlgebra F (skewSq F E) 0 →ₐ[F] E :=
  QuadraticAlgebra.lift ⟨skewRoot F E, by
    rw [zero_smul, add_zero, Algebra.smul_def, mul_one, algebraMap_skewSq]⟩

theorem skewLift_apply (z : QuadraticAlgebra F (skewSq F E) 0) :
    skewLift F E z = algebraMap F E z.re + algebraMap F E z.im * skewRoot F E := by
  rw [skewLift, QuadraticAlgebra.lift_apply_apply, Algebra.smul_def, Algebra.smul_def, mul_one]

theorem skewLift_bijective : Function.Bijective (skewLift F E) := by
  have hinj : Function.Injective (skewLift F E) := (skewLift F E).toRingHom.injective
  refine ⟨hinj, ?_⟩
  have := LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (skewLift F E).toLinearMap)
    (by rw [QuadraticAlgebra.finrank_eq_two, Algebra.IsQuadraticExtension.finrank_eq_two])
  exact this.mp hinj

/-- `F(√d) ≃ E`, sending `ω` to the skew root. -/
def quadraticEquiv : QuadraticAlgebra F (skewSq F E) 0 ≃ₐ[F] E :=
  AlgEquiv.ofBijective (skewLift F E) (skewLift_bijective F E)

theorem quadraticEquiv_apply (z : QuadraticAlgebra F (skewSq F E) 0) :
    quadraticEquiv F E z = skewLift F E z := rfl

@[simp] theorem quadraticEquiv_omega :
    quadraticEquiv F E (QuadraticAlgebra.omega) = skewRoot F E := by
  rw [quadraticEquiv_apply, skewLift_apply]
  simp

/-- The `F`-algebra map `E → A` sending the skew root to a square root `w` of `d` in `A`. -/
def liftSkew {A : Type*} [Ring A] [Algebra F A] (w : A)
    (hw : w * w = algebraMap F A (skewSq F E)) : E →ₐ[F] A :=
  (QuadraticAlgebra.lift ⟨w, by rw [zero_smul, add_zero, Algebra.smul_def, mul_one, hw]⟩).comp
    (quadraticEquiv F E).symm.toAlgHom

@[simp] theorem liftSkew_skewRoot {A : Type*} [Ring A] [Algebra F A] (w : A)
    (hw : w * w = algebraMap F A (skewSq F E)) : liftSkew F E w hw (skewRoot F E) = w := by
  have h : (quadraticEquiv F E).symm (skewRoot F E) = QuadraticAlgebra.omega :=
    (AlgEquiv.symm_apply_eq _).mpr (quadraticEquiv_omega F E).symm
  rw [liftSkew, AlgHom.comp_apply]
  change (QuadraticAlgebra.lift _) ((quadraticEquiv F E).symm (skewRoot F E)) = w
  rw [h, QuadraticAlgebra.lift_apply_apply]
  simp

/-- Every element of `E` is `a + b r` with `a, b ∈ F`. -/
theorem exists_eq_add_mul_skewRoot (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * skewRoot F E := by
  obtain ⟨z, rfl⟩ := (quadraticEquiv F E).surjective x
  exact ⟨z.re, z.im, by rw [quadraticEquiv_apply, skewLift_apply]⟩

end Langlands.CentralSimple.Landherr
