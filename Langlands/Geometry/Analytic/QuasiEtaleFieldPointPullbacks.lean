import Langlands.Geometry.Analytic.DomainEtalePullbacks
import Langlands.Geometry.Analytic.LocalizedEtaleFieldPointPullbackProof
import Langlands.Geometry.Analytic.LocalizedQuasiEtaleLocality
import Langlands.Geometry.Analytic.OpenImmersionFieldPointLifting

/-! # Full field points of quasi-étale pullbacks -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]

local notation "F" => localizedFieldPointFunctor (K := K) L

set_option backward.isDefEq.respectTransparency false in
private theorem fieldPoint_map_domainι_injective
    {Y : LocalizedCategory.{u, v, v} (K := K)} (D : (presentationOf Y).AnalyticDomain) :
    Function.Injective ((F).map (domainι Y D)) := by
  obtain ⟨S, rfl⟩ := localizedObjectEquiv.surjective Y
  exact fieldPoint_map_originalDomainInclusion_injective (L := L) D

/-- Full field points preserve the pullback defining a literal preimage domain. -/
theorem localizedFieldPoint_isPullback_domainPreimage
    {Y Z : LocalizedCategory.{u, v, v} (K := K)} (f : Y ⟶ Z)
    (D : (presentationOf Z).AnalyticDomain) :
    IsPullback ((F).map (domainι Y (domainPreimage f D))) ((F).map (domainPreimageMap f D))
      ((F).map f) ((F).map (domainι Z D)) := by
  refine (Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩
  · rw [← (F).map_comp, ← (F).map_comp, domainPreimageMap_comp_inclusion]
  · intro p q hpq
    exact fieldPoint_map_domainι_injective (L := L) _ hpq.1
  · intro p q hpq
    have hp : ((localizedFieldPointProjection L).app Y p).down ∈
        (domainPreimage f D).carrier := by
      change localizedSpaceFunctor.map f (((localizedFieldPointProjection L).app Y p).down) ∈
        D.carrier
      rw [← localizedFieldPointProjection_map_down, hpq,
        localizedFieldPointProjection_map_down, domainι_apply]
      exact (((localizedFieldPointProjection L).app (domainObj Z D) q).down).property
    obtain ⟨r, hr⟩ := exists_fieldPoint_lift_domainι (domainPreimage f D) p hp
    refine ⟨r, hr, fieldPoint_map_domainι_injective (L := L) D ?_⟩
    rw [← (F).map_comp_apply, domainPreimageMap_comp_inclusion, (F).map_comp_apply, hr]
    exact hpq

variable [CompleteSpace L] [IsUltrametricDist L] [IsAlgClosed L]
  {P A B X : LocalizedCategory.{u, v, v} (K := K)}
  {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ X} {g : B ⟶ X}

private theorem localizedFieldPoint_isPullback_of_domainEtale
    (h : IsPullback p q f g) (hf : HasDomainEtaleFactorization f) :
    IsPullback ((F).map p) ((F).map q) ((F).map f) ((F).map g) := by
  obtain ⟨W, _, w, ⟨D, e, rfl⟩, hw, rfl⟩ := hf
  let c := localizedEtalePullback w g hw
  have hc := IsPullback.of_isLimit c.2
  have hfield := localizedEtaleFieldPointPullback (K := K) (L := L)
    c.1.fst c.1.snd w g hw hc
  have hdomain := localizedFieldPoint_isPullback_domainPreimage (L := L) c.1.fst D
  have hr := isPullback_domainPreimage_comp hc D
  have hrfield : IsPullback ((F).map (domainPreimageMap c.1.fst D))
      ((F).map (domainι c.1.pt (domainPreimage c.1.fst D) ≫ c.1.snd))
      ((F).map (domainι W D ≫ w)) ((F).map g) := by
    simpa only [Functor.map_comp] using (hdomain.flip.paste_vert hfield)
  have h' : IsPullback (p ≫ e.hom) q (domainι W D ≫ w) g := by
    apply h.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) <;> simp [Category.assoc]
  let a := h'.isoIsPullback _ _ hr
  apply hrfield.of_iso' ((F).mapIso a) ((F).mapIso e) (Iso.refl _) (Iso.refl _)
  · simpa only [Functor.mapIso_hom, ← (F).map_comp] using
      congrArg (F).map (h'.isoIsPullback_hom_fst _ _ hr)
  · simpa only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id, ← (F).map_comp] using
      congrArg (F).map (h'.isoIsPullback_hom_snd _ _ hr)
  · simp [Category.assoc]
  · simp

/-- Full field points preserve any localized pullback with a quasi-étale
first leg. The field points are taken over one fixed complete algebraically
closed extension. -/
theorem localizedFieldPoint_isPullback_of_quasiEtale
    (h : IsPullback p q f g) (hf : quasiEtale f) :
    IsPullback ((F).map p) ((F).map q) ((F).map f) ((F).map g) := by
  have hcomm : (F).map p ≫ (F).map f = (F).map q ≫ (F).map g := by
    rw [← (F).map_comp, ← (F).map_comp, h.w]
  have hlift (a : (F).obj A) (b : (F).obj B) (hab : (F).map f a = (F).map g b) :
      ∃! z : (F).obj P, (F).map p z = a ∧ (F).map q z = b := by
    obtain ⟨s, _, hn, hs⟩ := isLocalizedQuasiEtaleAt_of_quasiEtale
      (S := presentationOf A) hf (((localizedFieldPointProjection L).app A a).down)
    obtain ⟨V, hV, ha⟩ := mem_sUnion.mp (mem_of_mem_nhds hn)
    obtain ⟨i, hi, W, w, j, hw, hj, hjw⟩ := hs V hV
    let D := (presentationOf A).chartDomain i
    have haD : ((localizedFieldPointProjection L).app A a).down ∈ D.carrier := by
      change (show (presentationOf A).presentation.space from
        ((localizedFieldPointProjection L).app A a).down) ∈
          range ((presentationOf A).presentation.atlas.chart i)
      rwa [hi]
    have hD : HasDomainEtaleFactorization (domainι A D ≫ f) :=
      ⟨W, j, w, hj.isAnalyticDomainEmbedding, hw, hjw⟩
    obtain ⟨a', ha'⟩ := exists_fieldPoint_lift_domainι D a haD
    have hr := localizedFieldPoint_isPullback_of_domainEtale (L := L)
      (isPullback_domainPreimage_comp h D) hD
    have hpre := localizedFieldPoint_isPullback_domainPreimage (L := L) p D
    have hab' : (F).map (domainι A D ≫ f) a' = (F).map g b := by
      rw [(F).map_comp_apply, ha', hab]
    obtain ⟨z, hz₁, hz₂⟩ := Types.exists_of_isPullback hr a' b hab'
    let k := domainι P (domainPreimage p D)
    refine ⟨(F).map k z, ⟨?_, ?_⟩, ?_⟩
    · rw [← (F).map_comp_apply, ← domainPreimageMap_comp_inclusion, (F).map_comp_apply, hz₁, ha']
    · simpa only [(F).map_comp_apply] using hz₂
    · rintro t ⟨ht₁, ht₂⟩
      obtain ⟨t', ht'₁, ht'₂⟩ := Types.exists_of_isPullback hpre t a' (ht₁.trans ha'.symm)
      have htz : t' = z := by
        apply Types.ext_of_isPullback hr
        · exact ht'₂.trans hz₁.symm
        · simpa only [(F).map_comp_apply, ht'₁, ht₂] using hz₂.symm
      exact ht'₁.symm.trans (congrArg ((F).map k) htz)
  refine (Types.isPullback_iff _ _ _ _).2 ⟨hcomm, ?_, fun a b hab => (hlift a b hab).exists⟩
  rintro r s ⟨hrs₁, hrs₂⟩
  have h := congrArg (fun l => l r) hcomm
  exact (hlift ((F).map p r) ((F).map q r) h).unique ⟨rfl, rfl⟩ ⟨hrs₁.symm, hrs₂.symm⟩

end Langlands.Analytic.SaturatedAtlasPresentation
