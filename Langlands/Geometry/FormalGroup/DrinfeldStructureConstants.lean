import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The universal coefficient ring for homogeneous Drinfeld structure constants -/

noncomputable section

namespace Langlands.FormalGroup.Drinfeld

open scoped BigOperators

variable {O : Type*} [CommRing O] (d : ℕ) (π : O)

local notation "PolynomialRing" => MvPolynomial (ℕ × Fin d) O

private def constantRelation : PolynomialRing :=
  (∏ i : Fin d, MvPolynomial.X ((0 : ℕ), i)) - MvPolynomial.C π

private def constantsIdeal : Ideal PolynomialRing := Ideal.span {constantRelation d π}

/-- The coefficient ring for sequences of structure constants with the prescribed leading product. -/
abbrev StructureConstantRing := PolynomialRing ⧸ constantsIdeal d π

/-- The universal structure constant at level `m` and degree `i`. -/
def structureConstant (m : ℕ) (i : Fin d) : StructureConstantRing d π :=
  Ideal.Quotient.mk _ (MvPolynomial.X (m, i))

theorem structureConstant_product :
    ∏ i : Fin d, structureConstant d π 0 i = algebraMap O (StructureConstantRing d π) π := by
  change (∏ i : Fin d, Ideal.Quotient.mk (constantsIdeal d π) (MvPolynomial.X (0, i))) =
    Ideal.Quotient.mk (constantsIdeal d π) (MvPolynomial.C π)
  apply sub_eq_zero.mp
  rw [← map_prod, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

section Evaluation

variable {B : Type*} [CommRing B] [Algebra O B] (a : ℕ → Fin d → B)

/-- Constants with the prescribed leading product induce the evaluation map of the quotient. -/
def structureConstantEval (ha : ∏ i : Fin d, a 0 i = algebraMap O B π) :
    StructureConstantRing d π →ₐ[O] B :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (fun ji : ℕ × Fin d => a ji.1 ji.2))
    (by
      intro f hf
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hf
      simp [constantRelation, ha])

@[simp]
theorem structureConstantEval_constant (ha : ∏ i : Fin d, a 0 i = algebraMap O B π)
    (m : ℕ) (i : Fin d) :
    structureConstantEval d π a ha (structureConstant d π m i) = a m i := by
  change MvPolynomial.aeval (fun ji : ℕ × Fin d => a ji.1 ji.2) (MvPolynomial.X (m, i)) = _
  rw [MvPolynomial.aeval_X]

/-- The universal constants determine a map from the quotient. -/
theorem structureConstantRing_algHom_ext {f g : StructureConstantRing d π →ₐ[O] B}
    (h : ∀ m i, f (structureConstant d π m i) = g (structureConstant d π m i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨m, i⟩
  exact h m i

end Evaluation

private theorem constant_dvd_of_map_quotient_eq_zero {σ : Type*} (g : MvPolynomial σ O)
    (h : MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {π})) g = 0) :
    MvPolynomial.C π ∣ g := by
  rw [← Ideal.mem_span_singleton, g.as_sum]
  apply Submodule.sum_mem
  intro s _
  have hs := congrArg (fun f : MvPolynomial σ (O ⧸ Ideal.span {π}) => f.coeff s) h
  rw [MvPolynomial.coeff_map] at hs
  change Ideal.Quotient.mk (Ideal.span {π}) (g.coeff s) = 0 at hs
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hs
  obtain ⟨u, hu⟩ := hs
  rw [Ideal.mem_span_singleton]
  refine ⟨MvPolynomial.monomial s u, ?_⟩
  rw [hu, MvPolynomial.C_mul_monomial]

/-- A prime uniformizer acts injectively on the universal coefficient ring. -/
theorem structureConstant_scalar_injective [IsDomain O] (hπ : Prime π) :
    Function.Injective (fun z : StructureConstantRing d π => π • z) := by
  have hzero (z : StructureConstantRing d π) (hz : π • z = 0) : z = 0 := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hm : Ideal.Quotient.mkₐ O (constantsIdeal d π) (π • f) = 0 :=
      (map_smul (Ideal.Quotient.mkₐ O (constantsIdeal d π)) π f).trans hz
    rw [Algebra.smul_def, MvPolynomial.algebraMap_eq] at hm
    change Ideal.Quotient.mk (constantsIdeal d π) (MvPolynomial.C π * f) = 0 at hm
    rw [Ideal.Quotient.eq_zero_iff_mem, constantsIdeal, Ideal.mem_span_singleton] at hm
    obtain ⟨g, hg⟩ := hm
    let J : Ideal O := Ideal.span {π}
    let : J.IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
    let reduce : PolynomialRing →+* MvPolynomial (ℕ × Fin d) (O ⧸ J) :=
      MvPolynomial.map (Ideal.Quotient.mk J)
    have hpi0 : reduce (MvPolynomial.C π) = 0 := by
      simp [reduce, J]
    have hmonomial : reduce (constantRelation d π) =
        ∏ i : Fin d, MvPolynomial.X (0, i) := by
      rw [constantRelation, map_sub, hpi0, sub_zero, map_prod]
      simp [reduce]
    have heq := congrArg reduce hg
    rw [map_mul, map_mul, hpi0, zero_mul, hmonomial] at heq
    have hmonomial_ne : (∏ i : Fin d, MvPolynomial.X (0, i) :
        MvPolynomial (ℕ × Fin d) (O ⧸ J)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => MvPolynomial.X_ne_zero _
    have hg0 : reduce g = 0 := (mul_eq_zero.mp heq.symm).resolve_left hmonomial_ne
    obtain ⟨b, hb⟩ := constant_dvd_of_map_quotient_eq_zero π g hg0
    have hf : f = constantRelation d π * b := by
      rw [hb, ← mul_left_comm] at hg
      exact mul_left_cancel₀ (fun h => hπ.ne_zero (MvPolynomial.C_eq_zero.mp h)) hg
    rw [Ideal.Quotient.eq_zero_iff_mem, constantsIdeal, Ideal.mem_span_singleton]
    exact ⟨b, hf⟩
  intro x y h
  change π • x = π • y at h
  apply sub_eq_zero.mp
  apply hzero
  rw [smul_sub, h, sub_self]

end Langlands.FormalGroup.Drinfeld
