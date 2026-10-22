import Langlands.Cohomology.Tate.InverseCosetSum
import Langlands.Cohomology.Tate.NegativeCorestriction

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

/-- The subgroup norm of the inverse-coset sum is the full group norm. -/
lemma subgroup_norm_inverseCosetSum (A : Rep.{u} R G) (a : A) :
    (Rep.res H.subtype A).ρ.norm (inverseCosetSum H A a) = A.ρ.norm a := by
  rw [inverseCosetSum_apply]
  exact (congrArg Subtype.val (invariantRestriction_normToInvariants H A a)).symm

/-- Inverse-coset sums carry full norm kernels into subgroup norm kernels. -/
lemma inverseCosetSum_normZero (A : Rep.{u} R G) (a : A) (ha : A.ρ.norm a = 0) :
    (Rep.res H.subtype A).ρ.norm (inverseCosetSum H A a) = 0 :=
  (subgroup_norm_inverseCosetSum H A a).trans ha

/-- At degree minus one, restriction is the actual inverse-coset sum on norm-kernel classes. -/
theorem restriction_minusOneClass (A : Rep.{u} R G) (a : A) (ha : A.ρ.norm a = 0) :
    restriction H A (-1) (minusOneClass A a ha) =
      minusOneClass (Rep.res H.subtype A) (inverseCosetSum H A a)
        (inverseCosetSum_normZero H A a ha) := by
  let b := coinducedDelta A a
  have hb : (shiftDownSequence A).g.hom b = a := coinducedProjection_delta A a
  obtain ⟨c, hc⟩ := invariant_lift_of_shortExact
    (shiftDownSequence_shortExact A) (normToInvariants (coinduced A) b)
    ((coefficient_norm_naturality (coinducedProjection A) b).trans
      ((congrArg A.ρ.norm hb).trans ha))
  have hbH : (shiftDownSequence A).g.hom (inverseCosetSum H (coinduced A) b) =
      inverseCosetSum H A a :=
    (inverseCosetSum_naturality H (coinducedProjection A) b).trans
      (congrArg (inverseCosetSum H A) hb)
  have hcH : (shiftDownSequence A).f.hom c =
      (Rep.res H.subtype (coinduced A)).ρ.norm (inverseCosetSum H (coinduced A) b) :=
    hc.trans (subgroup_norm_inverseCosetSum H (coinduced A) b).symm
  have hdG := delta_minusOneClass (shiftDownSequence_shortExact A) a ha b hb c hc
  have hdH := delta_minusOneClass (restrictedShiftDownSequence_shortExact H A)
    (inverseCosetSum H A a) (inverseCosetSum_normZero H A a ha)
    (inverseCosetSum H (coinduced A) b) hbH (invariantRestriction H (shiftDown A) c) hcH
  apply (restrictedShiftDownIso H A (-1)).toLinearEquiv.injective
  change TateCohomology.δ (restrictedShiftDownSequence_shortExact H A) (-1)
      (restriction H A (-1) (minusOneClass A a ha)) =
    TateCohomology.δ (restrictedShiftDownSequence_shortExact H A) (-1)
      (minusOneClass (Rep.res H.subtype A) (inverseCosetSum H A a)
        (inverseCosetSum_normZero H A a ha))
  exact (restriction_scalarSplit_delta H (shiftDownSequence A)
    (shiftDownSequence_scalarSplitting A) (-1) (minusOneClass A a ha)).symm.trans
      ((congrArg (restriction H (shiftDown A) 0) hdG).trans
        ((restrictionZero_zeroClass H c).trans hdH.symm))

end Langlands.Tate
