import Langlands.Geometry.Analytic.DomainEtaleFactorizations
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.SaturatedLocalizedIsomorphisms

/-! # Strong representatives of domain–étale factorizations -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A X : SaturatedAtlasPresentation.{u, v, v} K}

/-- A common strong presentation of the given source and a domain in a
strongly étale envelope, with equality of the actual strong composites. -/
structure RefinedDomainEtaleFactorization (f : A ⟶ X) where
  envelope : SaturatedAtlasPresentation.{u, v, v} K
  map : envelope ⟶ X
  isEtale : strongEtale map
  domain : envelope.AnalyticDomain
  source : SaturatedAtlasPresentation.{u, v, v} K
  toSource : source ⟶ A
  toDomain : source ⟶ envelope.domain domain
  toSource_isQuasiIso : toSource.IsQuasiIso
  toDomain_isQuasiIso : toDomain.IsQuasiIso
  comm : toSource ≫ f = toDomain ≫ envelope.domainInclusion domain ≫ map

/-- Realize the localized domain–étale factorization after a common
quasi-isomorphic refinement, keeping both coefficient maps strong. -/
def refinedDomainEtaleFactorization (f : A ⟶ X)
    (hf : HasDomainEtaleFactorization (localizationFunctor.map f)) :
    RefinedDomainEtaleFactorization f :=
  Classical.choice (show Nonempty (RefinedDomainEtaleFactorization f) from by
    obtain ⟨W, _, w, ⟨D, e, rfl⟩, hw, h⟩ := hf
    obtain ⟨W₀, hW₀⟩ := localizedObjectEquiv.surjective W
    change localizationFunctor.obj W₀ = W at hW₀
    subst W
    obtain ⟨φ, rfl⟩ := exists_localizedRightFraction w
    let eW := localizedQuasiIso φ.s φ.hs
    have hW : eW.hom ≫ localizedRightFraction φ = localizationFunctor.map φ.f :=
      localizationFunctor_map_s_comp_localizedRightFraction φ
    have hφ : strongEtale φ.f :=
      (etale_localizationFunctor_map_iff_strongEtale φ.f).mp
        (hW ▸ etale_comp (etale_of_isIso eW.hom) hw)
    let E : φ.X'.AnalyticDomain := domainPreimage eW.hom D
    let d := domainPreimageIso eW D
    let k : localizationFunctor.obj A ≅ localizationFunctor.obj (φ.X'.domain E) :=
      e ≪≫ d.symm
    have hd : d.hom ≫ domainι (localizationFunctor.obj W₀) D =
        localizationFunctor.map (φ.X'.domainInclusion E) ≫ eW.hom :=
      domainPreimageIso_hom_inclusion eW D
    have hk : k.hom ≫ localizationFunctor.map (φ.X'.domainInclusion E ≫ φ.f) =
        localizationFunctor.map f := by
      rw [Functor.map_comp, ← hW,
        ← Category.assoc (localizationFunctor.map (φ.X'.domainInclusion E)), ← hd]
      change (e.hom ≫ d.inv) ≫
        (d.hom ≫ domainι (localizationFunctor.obj W₀) D) ≫ localizedRightFraction φ = _
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
    let ψ := quasiIsoFractionOfIso k
    have hψ : localizationFunctor.map ψ.val.f = localizationFunctor.map ψ.val.s ≫ k.hom :=
      (localizationFunctor_map_s_comp_localizedRightFraction ψ.val).symm.trans
        (congrArg (localizationFunctor.map ψ.val.s ≫ ·)
          (localizedRightFraction_quasiIsoFractionOfIso k))
    have hmap : localizationFunctor.map (ψ.val.s ≫ f) =
        localizationFunctor.map (ψ.val.f ≫ φ.X'.domainInclusion E ≫ φ.f) := by
      rw [Functor.map_comp, Functor.map_comp, hψ, Category.assoc, hk]
    obtain ⟨R, r, hr, hR⟩ := (localizationFunctor_map_eq_iff _ _).mp hmap
    exact ⟨⟨φ.X', φ.f, hφ, E, R, r ≫ ψ.val.s, r ≫ ψ.val.f,
      (quasiIsomorphisms (K := K)).comp_mem _ _ hr ψ.val.hs,
      (quasiIsomorphisms (K := K)).comp_mem _ _ hr ψ.property,
      by simpa only [Category.assoc] using hR⟩⟩)

end Langlands.Analytic.SaturatedAtlasPresentation
