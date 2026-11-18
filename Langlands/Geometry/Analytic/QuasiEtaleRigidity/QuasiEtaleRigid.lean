import Langlands.Geometry.Analytic.QuasiEtaleRigidity.EtaleRigidity
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.LiftCompatibilityDeduction
import Langlands.Geometry.Analytic.QuasiEtaleDomainChartCover

/-! # Uniqueness in Berkovich's Key Lemma for compact quasi-étale spaces -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Transport

variable {U X Y : LocalizedCategory.{u, v, v} (K := K)}

/-- Rigidity is preserved by postcomposition with a monomorphism. -/
theorem IsRigidOn.comp_mono {p : U ⟶ X} {h : X ⟶ Y} [Mono h]
    {L : Set (localizedSpaceFunctor.obj U)} (hr : IsRigidOn p L) : IsRigidOn (p ≫ h) L := by
  obtain ⟨E, hEL, hE⟩ := hr
  exact ⟨E, hEL, fun V ψ ψ₁ ψ₂ h0 h1 h2 heq hn =>
    hE V ψ ψ₁ ψ₂ h0 h1 h2 ((cancel_mono h).1 (by simpa only [Category.assoc] using heq)) hn⟩

theorem IsRigidOn.isRigid {p : U ⟶ X} (hr : IsRigidOn p Set.univ) : IsRigid p := by
  obtain ⟨E, -, hE⟩ := hr
  exact ⟨E, fun V ψ ψ₁ ψ₂ heq hn => hE V ψ ψ₁ ψ₂ (Set.subset_univ _) (Set.subset_univ _)
    (Set.subset_univ _) heq hn⟩

theorem IsRigidOn.iso_comp_univ {W : LocalizedCategory.{u, v, v} (K := K)} {w : W ⟶ Y}
    (h : IsRigidOn w Set.univ) (e : U ≅ W) : IsRigidOn (e.hom ≫ w) Set.univ := by
  have := h.iso_comp e
  rwa [Set.preimage_univ] at this

theorem arrow_hom_eq {A B : LocalizedCategory.{u, v, v} (K := K)} {f : A ⟶ B} {p : U ⟶ X}
    (e : Arrow.mk f ≅ Arrow.mk p) : p = e.inv.left ≫ f ≫ e.hom.right := by
  have hw := Arrow.w e.hom
  simp only [Arrow.mk_hom] at hw
  rw [← hw, ← Category.assoc, Arrow.inv_hom_id_left, Category.id_comp]

end Transport

/-- The restriction of a quasi-étale strong map to a chart with a domain-étale factorization is
rigid. -/
theorem isRigidOn_chart_of_hasDomainEtaleFactorization {A B : AffinoidAtlasPresentation.{u, v, v} K}
    (g : ofSaturation A ⟶ ofSaturation B) (i : (ofSaturation A).presentation.atlas.Index)
    (hfac : HasDomainEtaleFactorization ((ofSaturation A).localizedDomainInclusion
      ((ofSaturation A).chartDomain i) ≫ localizationFunctor.map g)) :
    IsRigidOn ((ofSaturation A).localizedDomainInclusion ((ofSaturation A).chartDomain i) ≫
      localizationFunctor.map g) Set.univ := by
  obtain ⟨W, j, w, ⟨D, e₁, rfl⟩, hw, hjw⟩ := hfac
  obtain ⟨A₂, B₂, g₂, hg₂, ⟨eW⟩⟩ := hw
  let eWL : localizationFunctor.obj (ofSaturation A₂) ≅ W := Arrow.leftFunc.mapIso eW
  let dI := domainImageIso eWL.symm D
  let D₂ := domainPreimage eWL.symm.inv D
  -- compactness of `D₂`
  have hchart := (ofSaturation A).isCompactDomain_chartDomain i
  have : CompactSpace (localizedSpaceFunctor.obj (localizationFunctor.obj
      ((ofSaturation A).domain ((ofSaturation A).chartDomain i)))) :=
    isCompact_iff_compactSpace.mp hchart.1
  have : T2Space (localizedSpaceFunctor.obj (localizationFunctor.obj
      ((ofSaturation A).domain ((ofSaturation A).chartDomain i)))) := hchart.2
  let hh := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso (e₁ ≪≫ dI))
  have hD₂c : CompactSpace D₂.carrier := hh.compactSpace
  have hD₂t : T2Space D₂.carrier := hh.t2Space
  have hT4 : IsRigidOn (domainι (localizationFunctor.obj (ofSaturation A₂)) D₂ ≫
      localizationFunctor.map g₂) Set.univ :=
    @isRigidOn_domainInclusion_comp_etale K _ _ _ A₂ B₂ g₂ hg₂ D₂
      (isCompact_iff_compactSpace.mpr hD₂c) hD₂t
  have hrig := (hT4.iso_comp_univ (e₁ ≪≫ dI)).comp_mono (h := eW.hom.right)
  have hw' : eW.hom.left ≫ w = localizationFunctor.map g₂ ≫ eW.hom.right := by
    have := Arrow.w eW.hom
    simpa only [Arrow.mk_hom] using this
  have hdI : dI.hom ≫ domainι (localizationFunctor.obj (ofSaturation A₂)) D₂ =
      domainι W D ≫ eWL.symm.hom := domainImageIso_hom_inclusion eWL.symm D
  have hinv : eWL.symm.hom ≫ eW.hom.left = 𝟙 W := Arrow.inv_hom_id_left eW
  have hkey : ((e₁ ≪≫ dI).hom ≫ domainι (localizationFunctor.obj (ofSaturation A₂)) D₂ ≫
      localizationFunctor.map g₂) ≫ eW.hom.right = (e₁.hom ≫ domainι W D) ≫ w := by
    calc ((e₁ ≪≫ dI).hom ≫ domainι (localizationFunctor.obj (ofSaturation A₂)) D₂ ≫
          localizationFunctor.map g₂) ≫ eW.hom.right
        = e₁.hom ≫ (dI.hom ≫ domainι (localizationFunctor.obj (ofSaturation A₂)) D₂) ≫
            (localizationFunctor.map g₂ ≫ eW.hom.right) := by
          simp only [Iso.trans_hom, Category.assoc]
      _ = e₁.hom ≫ (domainι W D ≫ eWL.symm.hom) ≫ (eW.hom.left ≫ w) := by rw [hdI, hw']
      _ = e₁.hom ≫ domainι W D ≫ (eWL.symm.hom ≫ eW.hom.left) ≫ w := by
          simp only [Category.assoc]
      _ = (e₁.hom ≫ domainι W D) ≫ w := by rw [hinv, Category.id_comp, Category.assoc]
  rw [← hjw, ← hkey]
  exact hrig

/-- **Uniqueness in Berkovich's Key Lemma 7.2 (commutative diagrams).** A quasi-étale morphism
with compact source is rigid. -/
theorem isRigid_of_quasiEtale {U X : LocalizedCategory.{u, v, v} (K := K)} (p : U ⟶ X)
    (hp : quasiEtale p) (hU : IsCompactSpace U) : IsRigid p := by
  obtain ⟨A, B, g, hg, ⟨eArr⟩⟩ := hp
  let eL : localizationFunctor.obj (ofSaturation A) ≅ U := Arrow.leftFunc.mapIso eArr
  obtain ⟨hUc, hUt⟩ := hU
  let hh := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eL)
  have : CompactSpace A.space := hh.symm.compactSpace
  have : T2Space (ofSaturation A).presentation.space := hh.symm.t2Space
  obtain ⟨s, hs, hcov⟩ := hg.exists_finite_domainEtale_chart_cover
  have hR := isRigidOn_of_chart_cover g s hcov fun i hi =>
    isRigidOn_chart_of_hasDomainEtaleFactorization g i (hs i hi)
  have h := ((hR.iso_comp_univ eL.symm).comp_mono (h := eArr.hom.right)).isRigid
  rw [Category.assoc] at h
  rw [arrow_hom_eq eArr]
  exact h

end Langlands.Analytic.SaturatedAtlasPresentation
