import Langlands.Cohomology.Tate.ChainComparison
import Langlands.Cohomology.Tate.SplitTransfer

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

lemma coefficient_norm_naturality {A B : Rep.{u} R G} (f : A ⟶ B) (a : A) :
    f.hom (A.ρ.norm a) = B.ρ.norm (f.hom a) := by
  simp only [Representation.norm, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl (fun g _ => Rep.hom_comm_apply f g a)

omit [Fintype G] in
/-- An invariant in the kernel of a short exact sequence has an invariant preimage. -/
lemma invariant_lift_of_shortExact {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (b : S.X₂.ρ.invariants) (hb : S.g.hom b = 0) :
    ∃ c : S.X₁.ρ.invariants, S.f.hom c = b := by
  have he := (ShortComplex.moduleCat_exact_iff _).mp
    (hS.map_of_exact (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).exact
  obtain ⟨c, hc⟩ := he (b : S.X₂) hb
  have hi := (Rep.mono_iff_injective S.f).mp hS.mono_f
  refine ⟨⟨c, fun g => hi ?_⟩, hc⟩
  exact (Rep.hom_comm_apply S.f g c).trans
    ((congrArg (S.X₂.ρ g) hc).trans ((b.property g).trans hc.symm))

variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

/-- The full norm vanishes on a vector whose subgroup norm vanishes. -/
lemma normZero_of_subgroup_normZero (A : Rep.{u} R G) (a : A)
    (ha : (Rep.res H.subtype A).ρ.norm a = 0) : A.ρ.norm a = 0 := by
  have hz : normToInvariants (Rep.res H.subtype A) a = 0 := Subtype.ext ha
  have hh := cosetNorm_normToInvariants H A a
  rw [hz, map_zero] at hh
  exact (congrArg Subtype.val hh).symm

/-- At degree minus one, constructed corestriction is inclusion of norm-kernel representatives. -/
theorem corestriction_minusOneClass (A : Rep.{u} R G) (a : A)
    (ha : (Rep.res H.subtype A).ρ.norm a = 0) :
    corestriction H A (-1) (minusOneClass (Rep.res H.subtype A) a ha) =
      minusOneClass A a (normZero_of_subgroup_normZero H A a ha) := by
  let b := coinducedDelta A a
  have hb : (shiftDownSequence A).g.hom b = a := coinducedProjection_delta A a
  obtain ⟨c, hc⟩ := invariant_lift_of_shortExact
    (restrictedShiftDownSequence_shortExact H A)
    (normToInvariants (Rep.res H.subtype (coinduced A)) b)
    (by
      change (coinducedProjection A).hom ((Rep.res H.subtype (coinduced A)).ρ.norm b) = 0
      exact (coefficient_norm_naturality
        ((Rep.resFunctor H.subtype).map (coinducedProjection A)) b).trans
          ((congrArg (Rep.res H.subtype A).ρ.norm hb).trans ha))
  have hcInv :
      (Rep.invariantsFunctor R H).map
        ((Rep.resFunctor H.subtype).map (shiftDownSequence A).f) c =
      normToInvariants (Rep.res H.subtype (coinduced A)) b := Subtype.ext hc
  have hcg : (shiftDownSequence A).f.hom (cosetNorm H (shiftDown A) c) =
      (coinduced A).ρ.norm b := by
    have hh := cosetNorm_naturality H (shiftDownSequence A).f c
    rw [hcInv, cosetNorm_normToInvariants] at hh
    exact congrArg Subtype.val hh
  have hdH := delta_minusOneClass (restrictedShiftDownSequence_shortExact H A)
    a ha b hb c hc
  have hdG := delta_minusOneClass (shiftDownSequence_shortExact A)
    a (normZero_of_subgroup_normZero H A a ha) b hb
    (cosetNorm H (shiftDown A) c) hcg
  apply (shiftDownIso A (-1)).toLinearEquiv.injective
  change TateCohomology.δ (shiftDownSequence_shortExact A) (-1)
      (corestriction H A (-1) (minusOneClass (Rep.res H.subtype A) a ha)) =
    TateCohomology.δ (shiftDownSequence_shortExact A) (-1)
      (minusOneClass A a (normZero_of_subgroup_normZero H A a ha))
  exact (corestriction_scalarSplit_delta H (shiftDownSequence A)
    (shiftDownSequence_scalarSplitting A) (-1)
    (minusOneClass (Rep.res H.subtype A) a ha)).symm.trans
      ((congrArg (corestriction H (shiftDown A) 0) hdH).trans
        ((corestrictionZero_zeroClass H c).trans hdG.symm))

end Langlands.Tate
