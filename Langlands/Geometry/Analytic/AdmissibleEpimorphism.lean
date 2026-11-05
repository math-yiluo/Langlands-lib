import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidCoproduct
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Admissible bounded epimorphisms and actual norm-controlled lifts -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.BoundedAlgHom

variable {K : Type u} [NormedField K]
  {A : Type v} [NormedCommRing A] [Algebra K A]
  {B : Type w} [NormedCommRing B] [Algebra K B]
  (f : BoundedAlgHom K A B)

/-- The quotient seminorm at an image element, written directly as the
infimum of the norms of all representatives of that fiber. -/
def residueNorm (b : B) : ℝ :=
  sInf {r : ℝ | ∃ a : A, f a = b ∧ ‖a‖ = r}

theorem preimageNorms_bddBelow (b : B) :
    BddBelow {r : ℝ | ∃ a : A, f a = b ∧ ‖a‖ = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨a, _, rfl⟩
  exact norm_nonneg a

theorem preimageNorms_nonempty {b : B} (hb : ∃ a : A, f a = b) :
    {r : ℝ | ∃ a : A, f a = b ∧ ‖a‖ = r}.Nonempty := by
  obtain ⟨a, ha⟩ := hb
  exact ⟨‖a‖, a, ha, rfl⟩

theorem residueNorm_le (a : A) : f.residueNorm (f a) ≤ ‖a‖ :=
  csInf_le (f.preimageNorms_bddBelow (f a)) ⟨a, rfl, rfl⟩

/-- A bounded map already controls the image norm by a fixed multiple of
the quotient seminorm, on every fiber of a surjection. -/
theorem norm_le_mul_residueNorm (hf : Function.Surjective f) :
    ∃ M : ℝ, 0 < M ∧ ∀ b : B, ‖b‖ ≤ M * f.residueNorm b := by
  obtain ⟨M, hM, hbound⟩ := f.bounded
  refine ⟨M, hM, fun b => ?_⟩
  have hlow : ‖b‖ / M ≤ f.residueNorm b := by
    apply le_csInf (f.preimageNorms_nonempty (hf b))
    rintro r ⟨a, ha, rfl⟩
    apply (div_le_iff₀ hM).mpr
    have h := hbound a
    change ‖f a‖ ≤ M * ‖a‖ at h
    rw [ha] at h
    nlinarith
  exact (div_le_iff₀ hM).mp hlow |>.trans_eq (mul_comm _ _)

/-- A surjective bounded map is admissible when its fiber quotient
seminorm and the unchanged target norm bound one another uniformly. -/
def IsAdmissibleEpi : Prop :=
  Function.Surjective f ∧ ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧
    ∀ b : B, f.residueNorm b ≤ C * ‖b‖ ∧ ‖b‖ ≤ D * f.residueNorm b

/-- Equivalence of the source quotient-norm definition with uniform
norm-controlled representatives. The zero fiber is handled by zero. -/
theorem isAdmissibleEpi_iff_normControlledLifts :
    f.IsAdmissibleEpi ↔ ∃ C : ℝ, 0 < C ∧
      ∀ b : B, ∃ a : A, f a = b ∧ ‖a‖ ≤ C * ‖b‖ := by
  constructor
  · rintro ⟨hs, C, hC, D, hD, hbounds⟩
    refine ⟨2 * C, mul_pos (by norm_num) hC, fun b => ?_⟩
    by_cases hb : b = 0
    · subst b
      exact ⟨0, map_zero f.toAlgHom, by simp⟩
    · have hpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
      have hlt : f.residueNorm b < (2 * C) * ‖b‖ := by
        have hu := (hbounds b).1
        nlinarith [mul_pos hC hpos]
      obtain ⟨r, ⟨a, ha, har⟩, hr⟩ :=
        exists_lt_of_csInf_lt (f.preimageNorms_nonempty (hs b)) hlt
      exact ⟨a, ha, har.trans_le hr.le⟩
  · rintro ⟨C, hC, hlifts⟩
    have hs : Function.Surjective f := fun b => ⟨(hlifts b).choose, (hlifts b).choose_spec.1⟩
    obtain ⟨D, hD, hbound⟩ := f.norm_le_mul_residueNorm hs
    refine ⟨hs, C, hC, D, hD, fun b => ⟨?_, hbound b⟩⟩
    obtain ⟨a, ha, hnorm⟩ := hlifts b
    exact (ha ▸ f.residueNorm_le a).trans hnorm

/-- An actual bounded right inverse supplies all required representatives. -/
theorem isAdmissibleEpi_of_bounded_section (s : BoundedAlgHom K B A)
    (hs : f.comp s = BoundedAlgHom.id K B) : f.IsAdmissibleEpi := by
  apply f.isAdmissibleEpi_iff_normControlledLifts.mpr
  obtain ⟨C, hC, hnorm⟩ := s.bounded
  refine ⟨C, hC, fun b => ⟨s b, ?_, hnorm b⟩⟩
  exact congrArg (fun q : BoundedAlgHom K B B => q b) hs

theorem isAdmissibleEpi_id : (BoundedAlgHom.id K A).IsAdmissibleEpi := by
  apply (isAdmissibleEpi_iff_normControlledLifts _).mpr
  exact ⟨1, zero_lt_one, fun a => ⟨a, rfl, by simp⟩⟩

variable {C : Type z} [NormedCommRing C] [Algebra K C]
  (g : BoundedAlgHom K B C)

/-- Composite epimorphisms retain uniformly controlled lifts with the
product of the two positive constants. -/
theorem IsAdmissibleEpi.comp (hf : f.IsAdmissibleEpi) (hg : g.IsAdmissibleEpi) :
    (g.comp f).IsAdmissibleEpi := by
  obtain ⟨M, hM, hflifts⟩ := f.isAdmissibleEpi_iff_normControlledLifts.mp hf
  obtain ⟨N, hN, hglifts⟩ := g.isAdmissibleEpi_iff_normControlledLifts.mp hg
  apply (isAdmissibleEpi_iff_normControlledLifts _).mpr
  refine ⟨M * N, mul_pos hM hN, fun c => ?_⟩
  obtain ⟨b, hb, hnb⟩ := hglifts c
  obtain ⟨a, ha, hna⟩ := hflifts b
  refine ⟨a, ?_, ?_⟩
  · change g (f a) = c
    rw [ha, hb]
  · exact hna.trans ((mul_le_mul_of_nonneg_left hnb hM.le).trans_eq (mul_assoc _ _ _).symm)

end Langlands.Analytic.BoundedAlgHom

namespace Langlands.Analytic.PresentedAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K)

/-- Actual affinoid presentation quotients are admissible, with a uniform
constant two obtained from the quotient norm's small-excess lifts. -/
theorem presentationMap_isAdmissibleEpi : (presentationMap K A).IsAdmissibleEpi := by
  apply (BoundedAlgHom.isAdmissibleEpi_iff_normControlledLifts _).mpr
  refine ⟨2, by norm_num, fun a => ?_⟩
  by_cases ha : a = 0
  · subst a
    exact ⟨0, map_zero (presentationMap K A).toAlgHom, by simp⟩
  · obtain ⟨p, hp, hn⟩ := exists_representative_norm_lt K A a (norm_pos_iff.mpr ha)
    exact ⟨p, hp, by linarith⟩

variable [CompleteSpace K]

/-- The constructed affinoid coproduct diagonal is admissible with a
constant-one lifting bound, via its actual contractive left section. -/
theorem AffinoidCoproduct.diagonal_isAdmissibleEpi :
    (AffinoidCoproduct.diagonal K A).IsAdmissibleEpi := by
  apply (BoundedAlgHom.isAdmissibleEpi_iff_normControlledLifts _).mpr
  refine ⟨1, zero_lt_one, fun a => ?_⟩
  simpa only [one_mul] using AffinoidCoproduct.diagonal_preimage K A a

end Langlands.Analytic.PresentedAffinoidAlgebra
