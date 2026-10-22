import Langlands.Geometry.Analytic.Spectrum.Definitions
import Langlands.Geometry.Analytic.PowerBoundsDefinitions
import Mathlib.RingTheory.PowerBasis
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Polynomial.Lifts

/-! # Algebraic criteria for bounded powers -/

noncomputable section

universe u v w

namespace Langlands.Analytic

namespace HasBoundedPowers

variable {A : Type u} [NormedRing A] {a : A}

theorem of_norm_le_one [NormOneClass A] (ha : ‖a‖ ≤ 1) : HasBoundedPowers a :=
  ⟨1, zero_lt_one, fun n => (norm_pow_le a n).trans (pow_le_one₀ (norm_nonneg a) ha)⟩

/-- Nilpotence leaves only finitely many possibly nonzero powers. -/
theorem of_isNilpotent (ha : IsNilpotent a) : HasBoundedPowers a := by
  classical
  obtain ⟨d, hd⟩ := ha
  let C : ℝ := 1 + ∑ i ∈ Finset.range d, ‖a ^ i‖
  have hsum : 0 ≤ ∑ i ∈ Finset.range d, ‖a ^ i‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨C, add_pos_of_pos_of_nonneg zero_lt_one hsum, fun n => ?_⟩
  by_cases hn : n < d
  · exact (Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr hn)).trans
      (le_add_of_nonneg_left zero_le_one)
  · rw [pow_eq_zero_of_le (Nat.le_of_not_gt hn) hd, norm_zero]
    exact le_trans hsum (le_add_of_nonneg_left zero_le_one)

end HasBoundedPowers

/-- Bounded homomorphisms preserve bounded powers. -/
theorem BoundedRingHom.hasBoundedPowers_map {A : Type u} {B : Type v}
    [NormedCommRing A] [NormedCommRing B] (f : BoundedRingHom A B)
    {a : A} (ha : HasBoundedPowers a) : HasBoundedPowers (f a) := by
  obtain ⟨C, hC, hc⟩ := ha
  obtain ⟨D, hD, hd⟩ := f.bounded
  refine ⟨D * C, mul_pos hD hC, fun n => ?_⟩
  change ‖f.toRingHom a ^ n‖ ≤ _
  rw [← map_pow]
  exact (hd (a ^ n)).trans (mul_le_mul_of_nonneg_left (hc n) hD.le)

/-- The easy direction of the spectral criterion holds in every normed
commutative ring, without completeness or an affinoid presentation. -/
theorem HasBoundedPowers.spectrum_le_one {A : Type u} [NormedCommRing A]
    {a : A} (ha : HasBoundedPowers a) (x : BanachSpectrum A) : x a ≤ 1 := by
  obtain ⟨C, _, hc⟩ := ha
  by_contra! h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have hbound : (x a) ^ n ≤ C := by
    rw [← map_pow x.toMulRingSeminorm]
    exact (x.le_norm (a ^ n)).trans (hc n)
  exact hn.not_ge hbound

/-- A finite span over a coefficient ring with bounded image is norm bounded.
The ultrametric inequality prevents the number of summands from changing the
uniform bound. -/
theorem norm_le_of_mem_span_of_bounded_algebraMap
    {S : Type u} {A : Type v} [CommRing S] [NormedCommRing A]
    [IsUltrametricDist A] [Algebra S A] {ι : Type w} [Fintype ι]
    (v : ι → A) {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ s : S, ‖algebraMap S A s‖ ≤ D)
    {a : A} (ha : a ∈ Submodule.span S (Set.range v)) :
    ‖a‖ ≤ D * (1 + ∑ i, ‖v i‖) := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp ha
  rw [← hc]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg hD (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => norm_nonneg _)))
  intro i _
  rw [Algebra.smul_def]
  exact (norm_mul_le _ _).trans
    (mul_le_mul (hbound (c i))
      ((Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)).trans
        (le_add_of_nonneg_left zero_le_one))
      (norm_nonneg _) hD)

/-- An element integral over a subring with bounded image has bounded powers.
This is the algebraic final step in the affinoid spectral criterion. -/
theorem hasBoundedPowers_of_isIntegral_of_bounded_algebraMap
    {S : Type u} {A : Type v} [CommRing S] [Nontrivial S]
    [NormedCommRing A] [IsUltrametricDist A] [Algebra S A]
    {a : A} (ha : IsIntegral S a)
    (hb : ∃ D : ℝ, 0 < D ∧ ∀ s : S, ‖algebraMap S A s‖ ≤ D) :
    HasBoundedPowers a := by
  classical
  obtain ⟨D, hD, hb⟩ := hb
  let v : Fin (minpoly S a).natDegree → A := fun i => a ^ (i : ℕ)
  refine ⟨D * (1 + ∑ i, ‖v i‖),
    mul_pos hD (add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)), fun n => ?_⟩
  apply norm_le_of_mem_span_of_bounded_algebraMap v hD.le hb
  exact ha.mem_span_pow ⟨Polynomial.X ^ n, by simp⟩

/-- The same criterion with an explicit monic relation and coefficient map.
This avoids requiring a preselected algebra structure on the target. -/
theorem hasBoundedPowers_of_monic_relation
    {S : Type u} {A : Type v} [CommRing S] [Nontrivial S]
    [NormedCommRing A] [IsUltrametricDist A]
    (f : S →+* A) (a : A) (p : Polynomial S) (hp : p.Monic)
    (ha : p.eval₂ f a = 0)
    (hb : ∃ D : ℝ, 0 < D ∧ ∀ s : S, ‖f s‖ ≤ D) :
    HasBoundedPowers a := by
  let : Algebra S A := f.toAlgebra
  exact hasBoundedPowers_of_isIntegral_of_bounded_algebraMap
    (S := S) ⟨p, hp, ha⟩ hb

/-- The actual closed norm unit ball is a subring in an ultrametric ring. -/
def normUnitBallSubring (A : Type u) [NormedCommRing A] [NormOneClass A]
    [IsUltrametricDist A] : Subring A where
  carrier := {a | ‖a‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' ha hb := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  neg_mem' ha := by simpa using ha
  mul_mem' := by
    intro a b ha hb
    change ‖a‖ ≤ 1 at ha
    change ‖b‖ ≤ 1 at hb
    change ‖a * b‖ ≤ 1
    exact (norm_mul_le _ _).trans
      ((mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans
        (by simpa only [one_mul] using hb))

/-- A monic equation with coefficients in the norm unit ball gives bounded
powers. This proves the implication without assuming a spectral comparison. -/
theorem hasBoundedPowers_of_monic_norm_le_one
    {A : Type u} [NormedCommRing A] [NormOneClass A] [IsUltrametricDist A]
    [Nontrivial A] (a : A) (p : Polynomial A) (hp : p.Monic)
    (ha : p.eval a = 0) (hcoeff : ∀ i, ‖p.coeff i‖ ≤ 1) :
    HasBoundedPowers a := by
  let S := normUnitBallSubring A
  have hlift : p ∈ Polynomial.lifts S.subtype := by
    apply (Polynomial.lifts_iff_coeff_lifts p).mpr
    intro i
    exact ⟨⟨p.coeff i, by change ‖p.coeff i‖ ≤ 1; exact hcoeff i⟩, rfl⟩
  obtain ⟨q, hq, _, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hp
  apply hasBoundedPowers_of_monic_relation S.subtype a q hmonic
  · rw [← Polynomial.eval_map, hq]
    exact ha
  · refine ⟨1, zero_lt_one, fun s => ?_⟩
    have hs := s.property
    change ‖(s : A)‖ ≤ 1 at hs
    exact hs

end Langlands.Analytic
