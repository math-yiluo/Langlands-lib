import Langlands.Geometry.Analytic.GeneralizedAffinoid.Relations
import Langlands.Geometry.Analytic.AdmissibleEpimorphism

/-! # Actual presented closed quotients and bounded quotient recognition -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.ClosedQuotient

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) (J : Ideal A) [hJ : IsClosed (J : Set A)]

/-- Pull the closed ideal back through the unchanged weighted presentation. -/
def algebra : PresentedAffinoidAlgebra K where
  arity := A.arity
  polyradius := A.polyradius
  ideal := J.comap (presentationMap K A).toAlgHom.toRingHom
  ideal_closed := hJ.preimage (presentationMap K A).continuous

/-- The actual quotient map from the original affinoid algebra. -/
def map : BoundedAlgHom K A (algebra A J) := by
  letI := A.ideal_closed
  exact BoundedAlgHom.liftQuotient K A.ideal (presentationMap K (algebra A J))
    (by
      intro p hp
      apply (presentationMap_eq_zero_iff K (algebra A J) p).mpr
      change presentationMap K A p ∈ J
      rw [(presentationMap_eq_zero_iff K A p).mpr hp]
      exact J.zero_mem)

@[simp]
theorem map_presentationMap (p : GeneralizedTateAlgebra A.polyradius K) :
    map A J (presentationMap K A p) = presentationMap K (algebra A J) p := rfl

theorem map_comp_presentationMap :
    (map A J).comp (presentationMap K A) = presentationMap K (algebra A J) :=
  BoundedAlgHom.ext fun _ => rfl

theorem map_surjective : Function.Surjective (map A J) := by
  intro b
  obtain ⟨p, rfl⟩ := presentationMap_surjective K (algebra A J) b
  exact ⟨presentationMap K A p, rfl⟩

theorem norm_map_le (a : A) : ‖map A J a‖ ≤ ‖a‖ := by
  let := A.ideal_closed
  exact (BoundedAlgHom.quotient_norm_bound A.ideal (map A J).toAlgHom.toRingHom
    1 zero_lt_one (by
      intro p
      change ‖presentationMap K (algebra A J) p‖ ≤ 1 * ‖p‖
      exact (norm_presentationMap_le K (algebra A J) p).trans_eq (one_mul _).symm) a).trans_eq
    (one_mul _)

@[simp]
theorem map_eq_zero_iff (a : A) : map A J a = 0 ↔ a ∈ J := by
  obtain ⟨p, rfl⟩ := presentationMap_surjective K A a
  exact presentationMap_eq_zero_iff K (algebra A J) p

theorem ker_map : RingHom.ker (map A J).toAlgHom.toRingHom = J := by
  ext a
  exact map_eq_zero_iff A J a

/-- The target's small presentation representatives give controlled lifts
in the original algebra, without an open mapping theorem. -/
theorem map_isAdmissibleEpi : (map A J).IsAdmissibleEpi := by
  apply (map A J).isAdmissibleEpi_iff_normControlledLifts.mpr
  refine ⟨2, by norm_num, fun b => ?_⟩
  by_cases hb : b = 0
  · subst b
    exact ⟨0, map_zero (map A J).toAlgHom, by simp⟩
  · obtain ⟨p, hp, hnorm⟩ :=
      exists_representative_norm_lt K (algebra A J) b (norm_pos_iff.mpr hb)
    exact ⟨presentationMap K A p, hp, (norm_presentationMap_le K A p).trans
      (hnorm.le.trans_eq (two_mul _).symm)⟩

variable {E : Type v} [NormedCommRing E] [NormedAlgebra K E]
  (φ : BoundedAlgHom K A E) (hφ : ∀ a ∈ J, φ a = 0)

/-- Bounded descent out of the constructed presented quotient. -/
def lift : BoundedAlgHom K (algebra A J) E := by
  letI := (algebra A J).ideal_closed
  exact BoundedAlgHom.liftQuotient K (algebra A J).ideal
    (φ.comp (presentationMap K A)) (fun _ hp => hφ _ hp)

@[simp]
theorem lift_map (a : A) : lift A J φ hφ (map A J a) = φ a := by
  obtain ⟨p, rfl⟩ := presentationMap_surjective K A a
  rfl

theorem lift_comp_map : (lift A J φ hφ).comp (map A J) = φ :=
  BoundedAlgHom.ext (lift_map A J φ hφ)

/-- Every supplied positive bound descends unchanged to the actual quotient norm. -/
theorem norm_lift_le (C : ℝ) (hC : 0 < C)
    (hbound : ∀ a, ‖φ a‖ ≤ C * ‖a‖) (b : algebra A J) :
    ‖lift A J φ hφ b‖ ≤ C * ‖b‖ := by
  let := (algebra A J).ideal_closed
  apply BoundedAlgHom.quotient_norm_bound (algebra A J).ideal
    (lift A J φ hφ).toAlgHom.toRingHom C hC _ b
  intro p
  exact (hbound (presentationMap K A p)).trans
    (mul_le_mul_of_nonneg_left (norm_presentationMap_le K A p) hC.le)

variable {A J}

/-- Surjectivity of the actual quotient determines every bounded map from it. -/
theorem hom_ext (α β : BoundedAlgHom K (algebra A J) E)
    (h : α.comp (map A J) = β.comp (map A J)) : α = β := by
  apply BoundedAlgHom.ext
  intro b
  obtain ⟨a, rfl⟩ := map_surjective A J b
  exact congrArg (fun ψ : BoundedAlgHom K A E => ψ a) h

variable (A J)

/-- The presented quotient has the entire bounded-Hom quotient universal property. -/
def boundedHomEquiv :
    BoundedAlgHom K (algebra A J) E ≃
      {φ : BoundedAlgHom K A E // ∀ a ∈ J, φ a = 0} where
  toFun α := ⟨α.comp (map A J), fun a ha => by
    change α (map A J a) = 0
    rw [(map_eq_zero_iff A J a).mpr ha, map_zero]⟩
  invFun φ := lift A J φ.val φ.property
  left_inv α := hom_ext _ _ (lift_comp_map A J _ _)
  right_inv φ := Subtype.ext (lift_comp_map A J _ _)

/-- Identify any admissible quotient with this presented quotient when their
actual kernels agree. The inverse bound comes from controlled lifts. -/
def equivOfAdmissibleEpi (hker : RingHom.ker φ.toAlgHom.toRingHom = J)
    (hφepi : φ.IsAdmissibleEpi) : BoundedAlgEquiv K (algebra A J) E := by
  have hann : ∀ a ∈ J, φ a = 0 := by
    intro a ha
    exact (show a ∈ RingHom.ker φ.toAlgHom.toRingHom from hker ▸ ha)
  let ψ := lift A J φ hann
  have hbij : Function.Bijective ψ := by
    constructor
    · intro b c hbc
      obtain ⟨a, rfl⟩ := map_surjective A J b
      obtain ⟨d, rfl⟩ := map_surjective A J c
      have hzero : φ (a - d) = 0 := by
        rw [map_sub, sub_eq_zero]
        simpa only [ψ, lift_map] using hbc
      apply sub_eq_zero.mp
      rw [← map_sub]
      apply (map_eq_zero_iff A J (a - d)).mpr
      exact hker ▸ hzero
    · intro e
      obtain ⟨a, ha⟩ := hφepi.1 e
      exact ⟨map A J a, (lift_map A J φ hann a).trans ha⟩
  let e := AlgEquiv.ofBijective ψ.toAlgHom hbij
  refine {
    toAlgEquiv := e
    bounded := ψ.bounded
    inverse_bounded := ?_ }
  obtain ⟨C, hC, hlifts⟩ := φ.isAdmissibleEpi_iff_normControlledLifts.mp hφepi
  refine ⟨C, hC, fun b => ?_⟩
  obtain ⟨a, ha, hnorm⟩ := hlifts b
  have heq : e.symm b = map A J a := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact ((lift_map A J φ hann a).trans ha).symm
  change ‖e.symm b‖ ≤ C * ‖b‖
  rw [heq]
  exact (norm_map_le A J a).trans hnorm

end Langlands.Analytic.PresentedAffinoidAlgebra.ClosedQuotient
