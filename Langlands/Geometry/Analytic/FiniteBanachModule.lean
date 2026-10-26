import Langlands.Geometry.Analytic.TateUniversal.Definitions
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! # Finite coefficient maps and their Banach quotients -/

noncomputable section

open Topology

universe u v w

namespace Langlands.Analytic.BoundedAlgHom

section Coefficients

variable {K : Type u} {A : Type v} {B : Type w}
  [NormedField K] [NormedCommRing A] [NormedCommRing B]
  [NormedAlgebra K A] [NormedAlgebra K B]
  (f : BoundedAlgHom K A B) {n : ℕ}

/-- The actual coefficient map associated to a finite tuple in the target.
Its source has the finite-product norm. -/
def coefficientMap (b : Fin n → B) : (Fin n → A) →L[K] B where
  toFun c := ∑ i, f.toAlgHom (c i) * b i
  map_add' c d := by
    simp [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' t c := by
    simp [Pi.smul_apply, Finset.smul_sum]
  cont := continuous_finsetSum _ fun i _ =>
    (f.continuous.comp (continuous_apply i)).mul continuous_const

@[simp]
theorem coefficientMap_apply (b : Fin n → B) (c : Fin n → A) :
    f.coefficientMap b c = ∑ i, f (c i) * b i :=
  rfl

/-- Finiteness of this precise ring map is equivalent to surjectivity of
one of its finite coefficient maps. -/
theorem finite_iff_exists_surjective_coefficientMap :
    f.toAlgHom.toRingHom.Finite ↔
      ∃ (n : ℕ) (b : Fin n → B), Function.Surjective (f.coefficientMap b) := by
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  constructor
  · intro hf
    let : Module.Finite A B := hf
    obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := A) (M := B)
    refine ⟨n, b, ?_⟩
    exact (span_range_eq_top_iff_surjective_fintypeLinearCombination A b).mp hb
  · rintro ⟨n, b, hb⟩
    exact Module.Finite.of_surjective (Fintype.linearCombination A b) hb

end Coefficients

section Banach

variable {K : Type u} {A : Type v} {B : Type w}
  [NontriviallyNormedField K] [NormedCommRing A] [NormedCommRing B]
  [NormedAlgebra K A] [NormedAlgebra K B]
  [CompleteSpace A] [CompleteSpace B]
  (f : BoundedAlgHom K A B) {n : ℕ} (b : Fin n → B)

/-- A generating tuple gives coefficients with a uniform positive norm bound. -/
theorem coefficientMap_exists_preimage_norm_le
    (hb : Function.Surjective (f.coefficientMap b)) :
    ∃ C > 0, ∀ y : B, ∃ c : Fin n → A,
      f.coefficientMap b c = y ∧ ‖c‖ ≤ C * ‖y‖ :=
  (f.coefficientMap b).exists_preimage_norm_le hb

/-- The coefficient map for a generating tuple is open. -/
theorem coefficientMap_isOpenMap
    (hb : Function.Surjective (f.coefficientMap b)) :
    IsOpenMap (f.coefficientMap b) :=
  (f.coefficientMap b).isOpenMap hb

/-- The norm topology of the target is the quotient topology of the actual
finite coefficient map. -/
theorem coefficientMap_isQuotientMap
    (hb : Function.Surjective (f.coefficientMap b)) :
    IsQuotientMap (f.coefficientMap b) :=
  (f.coefficientMap b).isQuotientMap hb

/-- The canonical first-isomorphism map is an isomorphism of Banach spaces.
The quotient carries its usual quotient norm and topology. -/
def coefficientQuotientEquiv
    (hb : Function.Surjective (f.coefficientMap b)) :
    ((Fin n → A) ⧸ (f.coefficientMap b).ker) ≃L[K] B := by
  let L := f.coefficientMap b
  letI : IsClosed (L.ker : Set (Fin n → A)) := L.isClosed_ker
  let e := L.toLinearMap.quotKerEquivOfSurjective hb
  apply e.toContinuousLinearEquivOfContinuous
  apply L.toLinearMap.ker.isQuotientMap_mkQ.continuous_iff.mpr
  exact L.continuous

@[simp]
theorem coefficientQuotientEquiv_apply_mk
    (hb : Function.Surjective (f.coefficientMap b)) (c : Fin n → A) :
    f.coefficientQuotientEquiv b hb (Submodule.Quotient.mk c) =
      ∑ i, f (c i) * b i :=
  rfl

/-- Over a nontrivially normed field, algebraic module finiteness of a bounded
Banach algebra map is equivalent to a finite coefficient quotient map. -/
theorem finite_iff_exists_quotient_coefficientMap :
    f.toAlgHom.toRingHom.Finite ↔
      ∃ (n : ℕ) (b : Fin n → B), IsQuotientMap (f.coefficientMap b) := by
  rw [f.finite_iff_exists_surjective_coefficientMap]
  constructor
  · rintro ⟨n, b, hb⟩
    exact ⟨n, b, f.coefficientMap_isQuotientMap b hb⟩
  · rintro ⟨n, b, hb⟩
    exact ⟨n, b, hb.surjective⟩

end Banach

end Langlands.Analytic.BoundedAlgHom
