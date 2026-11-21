import Langlands.Geometry.Analytic.QuasiEtaleGeometricPointGeometry
import Langlands.Geometry.Analytic.DomainEtalePullbacks
import Langlands.Geometry.Analytic.LocalizedEtaleFieldPointPullbackProof
import Langlands.Geometry.Analytic.OpenImmersionFieldPointLifting

/-! # Full field-point preservation of quasi-étale pullbacks -/

noncomputable section

universe u v w uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Limits Topology

section Domains

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]

local notation "Φ" => localizedFieldPointFunctor (K := K) L

set_option backward.isDefEq.respectTransparency false in
/-- The full field-point map of an analytic domain inclusion is injective. -/
theorem localizedFieldPoint_map_domainι_injective {Y : LocalizedCategory.{u, v, w} (K := K)}
    (D : (presentationOf Y).AnalyticDomain) :
    Function.Injective (((Φ).map (domainι Y D)) : (Φ).obj (domainObj Y D) → (Φ).obj Y) := by
  obtain ⟨S, rfl⟩ := localizedObjectEquiv.surjective Y
  exact fieldPoint_map_originalDomainInclusion_injective (L := L) D

set_option backward.isDefEq.respectTransparency false in
/-- Taking full field points preserves the analytic pullback defining the inverse image of a
domain. -/
theorem isPullback_fieldPoint_domainPreimage
    {X Y : LocalizedCategory.{u, v, w} (K := K)} (f : X ⟶ Y)
    (D : (presentationOf Y).AnalyticDomain) :
    IsPullback ((Φ).map (domainι X (domainPreimage f D))) ((Φ).map (domainPreimageMap f D))
      ((Φ).map f) ((Φ).map (domainι Y D)) := by
  have h := domainPreimage_isPullback f D
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, fun _ _ hr => localizedFieldPoint_map_domainι_injective (L := L) _ hr.1, ?_⟩
  · simpa only [Functor.map_comp] using congrArg (Φ).map h.w
  · intro a b hab
    have ha : ((localizedFieldPointProjection L).app X a).down ∈ (domainPreimage f D).carrier := by
      change localizedSpaceFunctor.map f ((localizedFieldPointProjection L).app X a).down ∈ D.carrier
      rw [← localizedFieldPointProjection_map_down f, hab,
        localizedFieldPointProjection_map_down, domainι_apply]
      exact ((localizedFieldPointProjection L).app (domainObj Y D) b).down.property
    obtain ⟨r, hr⟩ := exists_fieldPoint_lift_domainι (domainPreimage f D) a ha
    refine ⟨r, hr, localizedFieldPoint_map_domainι_injective (L := L) D ?_⟩
    rw [← Functor.map_comp_apply, domainPreimageMap_comp_inclusion,
      Functor.map_comp_apply, hr, hab]

end Domains

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [IsAlgClosed L] [NormedAlgebra K L]

local notation "Φ" => localizedFieldPointFunctor (K := K) L

omit [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L] in
private theorem fieldPoint_isPullback_of_iso
    {P A B X P' A' B' X' : LocalizedCategory.{u, v, v} (K := K)}
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ X} {g : B ⟶ X}
    {p' : P' ⟶ A'} {q' : P' ⟶ B'} {f' : A' ⟶ X'} {g' : B' ⟶ X'}
    (h : IsPullback ((Φ).map p) ((Φ).map q) ((Φ).map f) ((Φ).map g))
    (eP : P ≅ P') (eA : A ≅ A') (eB : B ≅ B') (eX : X ≅ X')
    (hp : p ≫ eA.hom = eP.hom ≫ p') (hq : q ≫ eB.hom = eP.hom ≫ q')
    (hf : f ≫ eX.hom = eA.hom ≫ f') (hg : g ≫ eX.hom = eB.hom ≫ g') :
    IsPullback ((Φ).map p') ((Φ).map q') ((Φ).map f') ((Φ).map g') := by
  apply h.of_iso ((Φ).mapIso eP) ((Φ).mapIso eA) ((Φ).mapIso eB) ((Φ).mapIso eX)
  · simpa only [Functor.mapIso_hom, ← Functor.map_comp] using congrArg (Φ).map hp
  · simpa only [Functor.mapIso_hom, ← Functor.map_comp] using congrArg (Φ).map hq
  · simpa only [Functor.mapIso_hom, ← Functor.map_comp] using congrArg (Φ).map hf
  · simpa only [Functor.mapIso_hom, ← Functor.map_comp] using congrArg (Φ).map hg

set_option backward.isDefEq.respectTransparency false in
/-- Full field points preserve pullbacks along a map factoring as an analytic domain embedding
followed by an étale morphism. -/
theorem fieldPoint_isPullback_of_domainEtale
    {P A B X : LocalizedCategory.{u, v, v} (K := K)}
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ X} {g : B ⟶ X}
    (hf : HasDomainEtaleFactorization f) (hP : IsPullback p q f g) :
    IsPullback ((Φ).map p) ((Φ).map q) ((Φ).map f) ((Φ).map g) := by
  obtain ⟨W, _, w, ⟨D, e, rfl⟩, hw, rfl⟩ := hf
  let t := localizedEtalePullback w g hw
  have ht : IsPullback t.1.fst t.1.snd w g := IsPullback.of_isLimit t.2
  have hR := isPullback_domainPreimage_comp ht D
  have htF := localizedEtaleFieldPointPullback (K := K) (L := L) _ _ _ _ hw ht
  have hRF := (isPullback_fieldPoint_domainPreimage (L := L) t.1.fst D).flip.paste_vert htF
  have hRF' : IsPullback ((Φ).map (domainPreimageMap t.1.fst D))
      ((Φ).map (domainι t.1.pt (domainPreimage t.1.fst D) ≫ t.1.snd))
      ((Φ).map (domainι W D ≫ w)) ((Φ).map g) := by
    simpa only [Functor.map_comp] using hRF
  have hP' : IsPullback (p ≫ e.hom) q (domainι W D ≫ w) g := by
    apply hP.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    all_goals simp [Category.assoc]
  refine fieldPoint_isPullback_of_iso hRF' (hR.isoIsPullback _ _ hP') e.symm
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (· ≫ e.inv) (hR.isoIsPullback_hom_fst _ _ hP').symm
  · simpa only [Iso.refl_hom, Category.comp_id] using (hR.isoIsPullback_hom_snd _ _ hP').symm
  · simp [Category.assoc]
  · simp

set_option backward.isDefEq.respectTransparency false in
private theorem fieldPoint_isPullback_of_domainEtale_cover
    {P A B X : LocalizedCategory.{u, v, v} (K := K)}
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ X} {g : B ⟶ X}
    (hcharts : ∀ a : localizedSpaceFunctor.obj A,
      ∃ D : (presentationOf A).AnalyticDomain,
        a ∈ D.carrier ∧ HasDomainEtaleFactorization (domainι A D ≫ f))
    (hP : IsPullback p q f g) :
    IsPullback ((Φ).map p) ((Φ).map q) ((Φ).map f) ((Φ).map g) := by
  have localSquare (a : (Φ).obj A) : ∃ (D : (presentationOf A).AnalyticDomain)
      (a' : (Φ).obj (domainObj A D)), (Φ).map (domainι A D) a' = a ∧
      IsPullback ((Φ).map (domainPreimageMap p D))
        ((Φ).map (domainι P (domainPreimage p D) ≫ q))
        ((Φ).map (domainι A D ≫ f)) ((Φ).map g) := by
    obtain ⟨D, ha, hf⟩ := hcharts ((localizedFieldPointProjection L).app A a).down
    obtain ⟨a', ha'⟩ := exists_fieldPoint_lift_domainι D a ha
    exact ⟨D, a', ha', fieldPoint_isPullback_of_domainEtale hf (isPullback_domainPreimage_comp hP D)⟩
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Functor.map_comp] using congrArg (Φ).map hP.w
  · intro r s ⟨hp, hq⟩
    obtain ⟨D, a', ha', hD⟩ := localSquare ((Φ).map p r)
    have hpre := isPullback_fieldPoint_domainPreimage (L := L) p D
    obtain ⟨r', hr, hr'⟩ := Types.exists_of_isPullback hpre r a' ha'.symm
    obtain ⟨s', hs, hs'⟩ := Types.exists_of_isPullback hpre s a' (hp.symm.trans ha'.symm)
    have he : r' = s' := Types.ext_of_isPullback hD (hr'.trans hs'.symm) (by
      rw [Functor.map_comp_apply, Functor.map_comp_apply, hr, hs, hq])
    rw [← hr, ← hs, he]
  · intro a b hab
    obtain ⟨D, a', ha', hD⟩ := localSquare a
    obtain ⟨r', hr', hs'⟩ := Types.exists_of_isPullback hD a' b (by
      rw [Functor.map_comp_apply, ha', hab])
    refine ⟨(Φ).map (domainι P (domainPreimage p D)) r', ?_, ?_⟩
    · rw [← Functor.map_comp_apply, ← domainPreimageMap_comp_inclusion,
        Functor.map_comp_apply, hr', ha']
    · rw [← Functor.map_comp_apply]; exact hs'

set_option backward.isDefEq.respectTransparency false in
/-- The functor of full field points preserves every pullback square with a quasi-étale leg. -/
theorem localizedQuasiEtaleFieldPointPullback :
    LocalizedQuasiEtaleFieldPointPullbackStatement.{u, v, uL} K L := by
  intro P A B X p q f g hf hP
  obtain ⟨A₀, X₀, f₀, hf₀, ⟨e⟩⟩ := hf
  let eA : localizationFunctor.obj (ofSaturation A₀) ≅ A := Arrow.leftFunc.mapIso e
  let eX : localizationFunctor.obj (ofSaturation X₀) ≅ X := Arrow.rightFunc.mapIso e
  have he : eA.hom ≫ f = localizationFunctor.map f₀ ≫ eX.hom := e.hom.w
  have h₀ : IsPullback (p ≫ eA.inv) q (localizationFunctor.map f₀) (g ≫ eX.inv) := by
    apply hP.of_iso' (Iso.refl _) eA (Iso.refl _) eX
    · simp
    · simp
    · exact he
    · simp
  let A' := localizationFunctor.obj (ofSaturation A₀)
  have hcharts : ∀ a : localizedSpaceFunctor.obj A',
      ∃ D : (presentationOf A').AnalyticDomain,
        a ∈ D.carrier ∧ HasDomainEtaleFactorization (domainι A' D ≫ localizationFunctor.map f₀) := by
    intro a
    obtain ⟨σ, _, hσ, hfactor⟩ := hf₀.exists_local_domainEtale_charts a
    obtain ⟨V, hVσ, haV⟩ := Set.mem_sUnion.mp (mem_of_mem_nhds hσ)
    obtain ⟨i, hi, hiFactor⟩ := hfactor V hVσ
    refine ⟨(ofSaturation A₀).chartDomain i, ?_, hiFactor⟩
    rw [chartDomain_carrier, hi]
    exact haV
  have h₀F := fieldPoint_isPullback_of_domainEtale_cover (L := L) hcharts h₀
  refine fieldPoint_isPullback_of_iso h₀F (Iso.refl _) eA (Iso.refl _) eX ?_ ?_ ?_ ?_
  · simp
  · simp
  · exact he.symm
  · simp

end Langlands.Analytic.SaturatedAtlasPresentation
