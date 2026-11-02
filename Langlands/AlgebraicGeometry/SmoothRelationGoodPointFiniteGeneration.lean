import Langlands.AlgebraicGeometry.SmoothRelationGoodPointCotangent

/-! # Finite generation of the maximal ideal modulo base constants -/

noncomputable section

universe u v

open IsLocalRing

namespace Langlands.AlgebraicGeometry.SmoothRelationGoodPoint

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing B]
  [Algebra A B]

/-- At a rational point of an essentially finite type algebra, the maximal ideal
is generated modulo the extended base prime by finitely many elements. -/
lemma exists_finite_maximalIdeal_generators [Algebra.EssFiniteType A B]
    (hrat : IsRationalPoint A B) :
    ∃ N : Ideal B, N.FG ∧ N ≤ maximalIdeal B ∧
      maximalIdeal B ≤ ((maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) ⊔ N := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.essFiniteType_iff A B).mp
    (inferInstance : Algebra.EssFiniteType A B)
  let N : Ideal B := Ideal.span
    ((fun b : B ↦ b - constRep hrat b) '' (s : Set B))
  have hN : N.FG := Submodule.fg_span (s.finite_toSet.image _)
  have hNm : N ≤ maximalIdeal B := by
    rw [Ideal.span_le]
    rintro _ ⟨b, -, rfl⟩
    exact sub_constRep_mem hrat b
  have hconst : ∀ b ∈ Algebra.adjoin A (s : Set B),
      ∃ c : B, IsConst A c ∧ b - c ∈ N := by
    intro b hb
    induction hb using Algebra.adjoin_induction with
    | mem b hb =>
      exact ⟨constRep hrat b, constRep_isConst hrat b,
        Ideal.subset_span ⟨b, hb, rfl⟩⟩
    | algebraMap a =>
      exact ⟨algebraMap A B a, IsConst.const a, by simp⟩
    | add b b' _ _ hb hb' =>
      obtain ⟨c, hc, hbc⟩ := hb
      obtain ⟨c', hc', hbc'⟩ := hb'
      refine ⟨c + c', hc.add hc', ?_⟩
      convert add_mem hbc hbc' using 1
      ring
    | mul b b' _ _ hb hb' =>
      obtain ⟨c, hc, hbc⟩ := hb
      obtain ⟨c', hc', hbc'⟩ := hb'
      refine ⟨c * c', hc.mul hc', ?_⟩
      have heq : b * b' - c * c' = b * (b' - c') + c' * (b - c) := by ring
      rw [heq]
      exact add_mem (Ideal.mul_mem_left N b hbc') (Ideal.mul_mem_left N c' hbc)
  refine ⟨N, hN, hNm, ?_⟩
  intro z hz
  obtain ⟨t, -, htunit, hzt⟩ := hs z
  obtain ⟨c, hc, hzc⟩ := hconst (z * t) hzt
  have hcm : c ∈ maximalIdeal B := by
    have heq : c = z * t - (z * t - c) := by ring
    rw [heq]
    exact sub_mem (Ideal.mul_mem_right t (maximalIdeal B) hz) (hNm hzc)
  have hm : z * t ∈
      ((maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) ⊔ N := by
    have heq : z * t = c + (z * t - c) := by ring
    rw [heq]
    exact add_mem (Ideal.mem_sup_left (hc.mem_map hcm)) (Ideal.mem_sup_right hzc)
  exact (Ideal.mul_unit_mem_iff_mem _ htunit).mp hm

/-- The cotangent converse for an essentially finite type algebra at a rational point. -/
lemma maximalIdeal_eq_of_cotangentSpan_eq_top_of_essFiniteType [Algebra.EssFiniteType A B]
    (θ : A →+* B)
    (hθ : (maximalIdeal B).comap θ = (maximalIdeal B).comap (algebraMap A B))
    (hrat : IsRationalPoint A B) (hspan : cotangentSpan θ = ⊤) :
    maximalIdeal B = ((maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) ⊔
      ((maximalIdeal B).comap (algebraMap A B)).map θ :=
  maximalIdeal_eq_of_cotangentSpan_eq_top θ hθ hrat
    (exists_finite_maximalIdeal_generators hrat) hspan

/-- A finite ideal generating the maximal ideal modulo the extended base prime. -/
structure FiniteMaximalIdealData (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B] where
  ideal : Ideal B
  finitely_generated : ideal.FG
  le_maximal : ideal ≤ maximalIdeal B
  maximal_le : maximalIdeal B ≤
    ((maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) ⊔ ideal

/-- Choose finite maximal-ideal generators modulo the base prime at a rational point. -/
def finiteMaximalIdealData [Algebra.EssFiniteType A B] (hrat : IsRationalPoint A B) :
    FiniteMaximalIdealData A B := by
  exact Classical.choice (by
    obtain ⟨N, hN, hNm, hmN⟩ := exists_finite_maximalIdeal_generators hrat
    exact ⟨⟨N, hN, hNm, hmN⟩⟩)

end Langlands.AlgebraicGeometry.SmoothRelationGoodPoint
