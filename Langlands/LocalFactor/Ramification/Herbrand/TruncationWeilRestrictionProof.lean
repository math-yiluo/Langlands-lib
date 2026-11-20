import Langlands.LocalFactor.Ramification.Herbrand.TruncationWeilQuotientProof
import Langlands.VirtualRepresentation.Weil.GroupTransport

/-! # Restriction of Weil representations through a transitivity index -/

noncomputable section

namespace Langlands.Ramification.Kummer

open LocalClassField HerbrandBridge Weil.Local
open VirtualRepresentation.LocalWeil.Ramification

universe u v

variable {p : ℕ} [Fact p.Prime]

local instance weilUpperGroupNormal (F : PadicField.{u} p) (r : ℝ) : (upperGroup F r).Normal :=
  Subgroup.Normal.comap inferInstance _

/-- Factor a Weil action through the upper ramification quotient on the same carrier. -/
private def descendToWeilQuotient {F : PadicField.{u} p} {μ : ℝ}
    (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)) (hA : IsTrivialAt F A μ) :
    FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F ⧸ upperGroup F μ) :=
  FiniteRepresentation.of (QuotientGroup.lift _ A.representation (fun w hw => hA w hw))

private theorem descendToWeilQuotient_isContinuous {F : PadicField.{u} p} {μ : ℝ}
    {A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)} (hA : IsTrivialAt F A μ)
    (hcont : A.IsContinuous) : (descendToWeilQuotient A hA).IsContinuous := by
  let B := descendToWeilQuotient A hA
  let : TopologicalSpace (Module.End ℂ B) := moduleTopology ℂ (Module.End ℂ B)
  change Continuous B.representation
  rw [(QuotientGroup.isQuotientMap_mk (upperGroup F μ)).continuous_iff]
  exact hcont

/-- Restriction gives a bijection of the continuous classes trivial at the
transitivity index and preserves irreducibility and all upper fixed-space ranks. -/
theorem truncationWeilRestriction : TruncationWeilRestrictionStatement.{u, v} := by
  intro p _ F E μ htrans hμ
  let K := E.asPadicField (p := p)
  let : (upperGroup K μ).Normal := weilUpperGroupNormal K μ
  let ι := (intermediateWeilMap F E).toMonoidHom
  let mkF := QuotientGroup.mk' (upperGroup F μ)
  let mkE := QuotientGroup.mk' (upperGroup K μ)
  let toQuotient := mkF.comp ι
  obtain ⟨φ, hφ, hfiltration⟩ := truncationWeilQuotient p F E μ htrans μ hμ le_rfl
  change ∀ w : localWeilGroup K, φ (mkE w) = toQuotient w at hφ
  have hsurj : Function.Surjective toQuotient := by
    intro q
    obtain ⟨a, rfl⟩ := φ.surjective q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (upperGroup K μ) a
    exact ⟨w, (hφ w).symm⟩
  have hrestrict (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F))
      (hA : IsTrivialAt F A μ) : IsTrivialAt K (weilRestrict E A) μ := by
    intro w hw
    have hw' : mkE w = 1 := (QuotientGroup.eq_one_iff w).mpr hw
    change A.representation (ι w) = 1
    apply hA
    refine (QuotientGroup.eq_one_iff (ι w)).mp ?_
    change toQuotient w = 1
    rw [← hφ w, hw', map_one]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨A, hcont, hA, rfl⟩
    exact ⟨weilRestrict E A, weilRestrict_isContinuous E hcont, hrestrict A hA, rfl⟩
  · rintro _ ⟨A, _, hA, rfl⟩ _ ⟨B, _, hB, rfl⟩ hab
    obtain ⟨e⟩ := (FiniteRepresentation.classOf_eq_iff (weilRestrict E A) (weilRestrict E B)).mp hab
    let Aquot := descendToWeilQuotient A hA
    let Bquot := descendToWeilQuotient B hB
    apply (FiniteRepresentation.classOf_eq_iff A B).mpr
    refine ⟨Representation.Equiv.mk e.toLinearEquiv fun w => ?_⟩
    obtain ⟨w', hw'⟩ := hsurj (mkF w)
    change e.toLinearEquiv.toLinearMap ∘ₗ Aquot.representation (mkF w) =
      Bquot.representation (mkF w) ∘ₗ e.toLinearEquiv.toLinearMap
    rw [← hw']
    exact e.isIntertwining' w'
  · rintro _ ⟨B, hcont, hB, rfl⟩
    let Bquot := descendToWeilQuotient B hB
    let fromF := φ.symm.toMulEquiv.toMonoidHom.comp mkF
    let A := FiniteRepresentation.restrict fromF Bquot
    have hAcont : A.IsContinuous :=
      FiniteRepresentation.isContinuous_restrict fromF
        (φ.symm.continuous.comp QuotientGroup.continuous_mk)
        (descendToWeilQuotient_isContinuous hB hcont)
    have hA : IsTrivialAt F A μ := by
      intro w hw
      have hw' : mkF w = 1 := (QuotientGroup.eq_one_iff w).mpr hw
      change Bquot.representation (φ.symm (mkF w)) = 1
      rw [hw', map_one, map_one]
    refine ⟨FiniteRepresentation.classOf A, ⟨A, hAcont, hA, rfl⟩, ?_⟩
    have hcomp : fromF.comp ι = mkE := by
      ext w
      change φ.symm (toQuotient w) = mkE w
      rw [← hφ w, φ.symm_apply_apply]
    change FiniteRepresentation.classOf (FiniteRepresentation.restrict (fromF.comp ι) Bquot) =
      FiniteRepresentation.classOf B
    rw [hcomp]
    rfl
  · intro A hA
    let Aquot := descendToWeilQuotient A hA
    constructor
    · change (FiniteRepresentation.restrict toQuotient Aquot).IsIrreducible ↔
        (FiniteRepresentation.restrict mkF Aquot).IsIrreducible
      exact (FiniteRepresentation.isIrreducible_restrict_iff _ hsurj Aquot).trans
        (FiniteRepresentation.isIrreducible_restrict_iff _ (QuotientGroup.mk'_surjective _) Aquot).symm
    · intro r hr
      have hfixed : upperFixedSpace K (weilRestrict E A) r = upperFixedSpace F A r := by
        by_cases hrμ : r ≤ μ
        · have hmap : (toQuotient : localWeilGroup K → _) = φ ∘ mkE :=
            funext fun w => (hφ w).symm
          have himage : toQuotient '' (upperGroup K r : Set (localWeilGroup K)) =
              mkF '' (upperGroup F r : Set (localWeilGroup F)) := by
            rw [hmap]
            have h := hfiltration r hr hrμ
            rw [Set.image_image] at h
            exact h
          apply Submodule.ext
          intro z
          refine (mem_upperFixedSpace K (weilRestrict E A) r z).trans
            (Iff.trans ?_ (mem_upperFixedSpace F A r z).symm)
          change (∀ w ∈ upperGroup K r, Aquot.representation (toQuotient w) z = z) ↔
            ∀ w ∈ upperGroup F r, Aquot.representation (mkF w) z = z
          calc
            _ ↔ ∀ q ∈ toQuotient '' (upperGroup K r : Set (localWeilGroup K)),
                Aquot.representation q z = z := Set.forall_mem_image.symm
            _ ↔ _ := by
              rw [himage]
              exact Set.forall_mem_image
        · have hμr := (lt_of_not_ge hrμ).le
          have htopF := (upperFixedSpace_eq_top_iff F A r).mpr (isTrivialAt_mono F A hμr hA)
          have htopE := (upperFixedSpace_eq_top_iff K (weilRestrict E A) r).mpr
            (isTrivialAt_mono K (weilRestrict E A) hμr (hrestrict A hA))
          exact htopE.trans htopF.symm
      exact congrArg (fun S : Submodule ℂ A => Module.finrank ℂ S) hfixed

end Langlands.Ramification.Kummer
