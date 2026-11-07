import Langlands.Representation.CuspidalSupport.OpenNormalFamilyProjector
import Langlands.Representation.Induction.OpenAdjunction

/-! Support of compact induction of a finite compact restriction. -/

noncomputable section

open CategoryTheory

namespace Langlands.CuspidalSupport

universe uG uV uF

section OpenNormal

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G] (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G))
  (π : SmoothRep.{0, uG, uV} ℂ G)
  (hc : HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup N π).representation)
  {m : ℕ} (W : Fin m → Subrepresentation (π.representation.comp N.subtype))
  (hWirr : ∀ i, (W i).toRepresentation.IsIrreducible)
  (hWspan : (⨆ i, (W i).toSubmodule) = ⊤)

/-- Compact induction of the full restriction, with its actual function carrier. -/
abbrev openNormalRestrictionCompactInduction : SmoothRep.{0, uG, max uG uV} ℂ G :=
  SmoothRep.of (Induction.compactInduced N (π.representation.comp N.subtype))
    (Induction.compactInduced_smooth _ _)

set_option maxHeartbeats 800000 in
/-- The finite-family projector fixes the actual compact induction of the full
restriction. Naturality on the subgroup unit extends to all functions by the
coset-sum identity. -/
theorem openNormalFamilyProjector_fixes_compactInduction
    (v : openNormalRestrictionCompactInduction N π) :
    openNormalFamilyProjector N hN π hc W hWirr hWspan
      (openNormalRestrictionCompactInduction N π) v = v := by
  let C := openNormalRestrictionCompactInduction N π
  let σ := π.representation.comp N.subtype
  let U := Induction.unitMap N hN σ (SmoothRep.restrictSubgroup N π).isSmooth
  let p := openNormalFamilyProjector N hN π hc W hWirr hWspan C
  have hunit : (Induction.resIntertwining N C.representation p).comp U = U := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    have hn := CompactCoefficientClass.selectedProjectorOfIsCompl_natural
      (CompactCoefficientClass.classesOfFiniteFamily
        (openNormalFamilyObject N hN π hc W hWirr))
      (fun c => openSubgroup_isCompl_isotypic_annihilator N hN c.val
        (SmoothRep.restrictSubgroup N π))
      (fun c => openSubgroup_isCompl_isotypic_annihilator N hN c.val
        (SmoothRep.restrictSubgroup N C)) U w
    have hb := CompactCoefficientClass.finiteFamilyAmbientProjector_fixes_base N
      (openNormalFamilyObject N hN π hc W hWirr) π
      (openNormalFamilyInclusion N hN π hc W hWirr)
      (openNormalFamilyInclusion_injective N hN π hc W hWirr)
      (openNormalFamilyInclusion_span N hN π hc W hWirr hWspan)
      (fun c => openSubgroup_isCompl_isotypic_annihilator N hN c.val
        (SmoothRep.restrictSubgroup N π)) w
    exact hn.trans (congrArg U hb)
  have hn := Induction.cosetSum_resIntertwining_comp N hN C.representation σ p U v
  have hsum : Induction.cosetSum N hN C.representation σ U v = v :=
    Induction.cosetSum_unitMap N hN σ (SmoothRep.restrictSubgroup N π).isSmooth v
  change p v = v
  calc
    p v = p (Induction.cosetSum N hN C.representation σ U v) := congrArg p hsum.symm
    _ = Induction.cosetSum N hN C.representation σ
        ((Induction.resIntertwining N C.representation p).comp U) v := hn.symm
    _ = Induction.cosetSum N hN C.representation σ U v :=
      congrArg (fun a => Induction.cosetSum N hN C.representation σ a v) hunit
    _ = v := hsum

include hN hc W hWirr hWspan in
/-- Every irreducible actual subquotient of this compact induction has a
nonzero restricted intertwiner into the original representation. -/
theorem openNormalFamily_compactInduction_subquotient_restricted_hom
    (D : SmoothRep.{0, uG, max uG uV} ℂ G) (hD : D.IsIrreducible)
    (hDC : SmoothRep.IsSubquotient D (openNormalRestrictionCompactInduction N π)) :
    ∃ q : (SmoothRep.restrictSubgroup N D).representation.IntertwiningMap
        (SmoothRep.restrictSubgroup N π).representation, q ≠ 0 := by
  apply (openNormalFamilyProjector_fixes_iff N hN π hc W hWirr hWspan D hD).mp
  obtain ⟨B, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDC
  have hB : ∀ v : B,
      openNormalFamilyProjector N hN π hc W hWirr hWspan B v = v := by
    intro v
    apply hi
    exact (openNormalFamilyProjector_natural N hN π hc W hWirr hWspan
      (SmoothRep.hom i) v).symm.trans
        (openNormalFamilyProjector_fixes_compactInduction N hN π hc W hWirr hWspan
          (SmoothRep.hom i v))
  intro v
  obtain ⟨w, rfl⟩ := hq v
  exact (openNormalFamilyProjector_natural N hN π hc W hWirr hWspan
    (SmoothRep.hom q) w).trans (congrArg (SmoothRep.hom q) (hB w))

end OpenNormal

end Langlands.CuspidalSupport
