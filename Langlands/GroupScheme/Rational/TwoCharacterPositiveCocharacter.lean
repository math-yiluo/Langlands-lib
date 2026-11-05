import Langlands.GroupScheme.Rational.IndependentStandardCocharacter
import Langlands.GroupScheme.Rational.RootFiniteness
import Langlands.LinearAlgebra.RationalRealSpan

/-! # A cocharacter positive on two characters outside opposite rays -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.LinearAlgebra

/-- Two nonzero rational vectors outside opposite rational rays admit one
rational functional strictly positive on both. -/
theorem exists_dual_pos_pair_of_not_neg_smul
    {V : Type*} [AddCommGroup V] [Module ℚ V] {a b : V}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : ∀ q : ℚ, q < 0 → b ≠ q • a) :
    ∃ f : V →ₗ[ℚ] ℚ, 0 < f a ∧ 0 < f b := by
  classical
  by_cases hlin : LinearIndependent ℚ ![a, b]
  · obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one
      (linearIndepOn_univ_iff.mpr hlin)
    refine ⟨f, ?_, ?_⟩
    · have hfa : f a = 1 := by simpa using hf 0 (Set.mem_univ _)
      rw [hfa]
      norm_num
    · have hfb : f b = 1 := by simpa using hf 1 (Set.mem_univ _)
      rw [hfb]
      norm_num
  · have hdep : ∃ q : ℚ, q • a = b := by
      simpa only [LinearIndependent.pair_iff' ha, not_forall, not_not] using hlin
    obtain ⟨q, hq⟩ := hdep
    have hq0 : q ≠ 0 := by
      intro h
      exact hb (by simpa [h] using hq.symm)
    have hqpos : 0 < q :=
      lt_of_le_of_ne (le_of_not_gt fun hneg => hab q hneg hq.symm) hq0.symm
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ ha
    refine ⟨f, by simp [hf], ?_⟩
    simpa [← hq, hf] using hqpos

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Two nonzero actual characters of a split torus admit a common positive
cocharacter if their images in the real character space are not opposite rays. -/
theorem IsSplitTorus.exists_cocharacter_pos_pair_of_not_opposite
    (hT : IsSplitTorus T.toGrp) (a b : characterLattice T)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : ∀ r : ℝ, 0 < r →
      (1 : ℝ) ⊗ₜ[ℤ] b ≠ -(r • (1 : ℝ) ⊗ₜ[ℤ] a)) :
    ∃ ν : cocharacterLattice T,
      0 < latticePairing T a ν ∧ 0 < latticePairing T b ν := by
  have haQ : toRat a ≠ 0 := by
    intro h
    exact ha (hT.character_toRat_injective (h.trans (map_zero toRat).symm))
  have hbQ : toRat b ≠ 0 := by
    intro h
    exact hb (hT.character_toRat_injective (h.trans (map_zero toRat).symm))
  have habQ : ∀ q : ℚ, q < 0 → toRat b ≠ q • toRat a := by
    intro q hq heq
    have hreal := congrArg (toReal (characterLattice T)) heq
    rw [toReal_toRat, map_smul, toReal_toRat, ← Rat.cast_smul_eq_qsmul ℝ] at hreal
    apply hab (-(q : ℝ)) (by exact_mod_cast neg_pos.mpr hq)
    simpa only [neg_smul, TensorProduct.neg_tmul, neg_neg] using hreal
  obtain ⟨f, hfa, hfb⟩ :=
    Langlands.LinearAlgebra.exists_dual_pos_pair_of_not_neg_smul haQ hbQ habQ
  obtain ⟨d, hd, ν, hν⟩ := hT.exists_positive_multiple_pairing f
  have hdQ : 0 < (d : ℚ) := by exact_mod_cast hd
  refine ⟨ν, ?_, ?_⟩
  · have h := mul_pos hdQ hfa
    rw [← hν a] at h
    exact_mod_cast h
  · have h := mul_pos hdQ hfb
    rw [← hν b] at h
    exact_mod_cast h

/-- A chosen actual cocharacter positive on the supplied two nonopposite
nonzero characters. No canonicity is asserted. -/
def positiveCocharacterOfNotOpposite
    (hT : IsSplitTorus T.toGrp) (a b : characterLattice T)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : ∀ r : ℝ, 0 < r →
      (1 : ℝ) ⊗ₜ[ℤ] b ≠ -(r • (1 : ℝ) ⊗ₜ[ℤ] a)) :
    cocharacterLattice T :=
  (hT.exists_cocharacter_pos_pair_of_not_opposite a b ha hb hab).choose

/-- Both actual integral lattice pairings of the chosen cocharacter are
strictly positive. -/
theorem positiveCocharacterOfNotOpposite_spec
    (hT : IsSplitTorus T.toGrp) (a b : characterLattice T)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : ∀ r : ℝ, 0 < r →
      (1 : ℝ) ⊗ₜ[ℤ] b ≠ -(r • (1 : ℝ) ⊗ₜ[ℤ] a)) :
    0 < latticePairing T a (positiveCocharacterOfNotOpposite hT a b ha hb hab) ∧
      0 < latticePairing T b (positiveCocharacterOfNotOpposite hT a b ha hb hab) :=
  (hT.exists_cocharacter_pos_pair_of_not_opposite a b ha hb hab).choose_spec

end Langlands.GroupScheme
