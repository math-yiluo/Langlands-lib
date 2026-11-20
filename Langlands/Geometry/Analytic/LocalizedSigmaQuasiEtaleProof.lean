import Langlands.Geometry.Analytic.LocalizedSigmaNearness
import Langlands.Geometry.Analytic.LocalizedQuasiEtaleLocality
import Langlands.Geometry.Analytic.DisjointUnionDomainEmbeddings
import Langlands.Geometry.Analytic.LocalizedSigmaEtaleDesc
import Langlands.Geometry.Analytic.LocalizedSigmaQuasiEtaleStatement

/-! # Quasi-étale and étale morphisms out of disjoint unions -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits Topology

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {J : Type z}

/-- The base map of a saturated inclusion of the chosen disjoint union is open. -/
theorem isOpenMap_sigmaCofan_inj_baseMap
    (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K) (j : J) :
    IsOpenMap ((sigmaCofan T).inj j).baseMap :=
  isOpenMap_sigmaMk (σ := fun j => (T j).presentation.space)

/-- A morphism out of a disjoint union of analytic spaces whose restriction to every piece is
quasi-étale is quasi-étale. -/
theorem quasiEtale_sigmaDesc (Y : J → LocalizedCategory.{u, max z v, max z v} (K := K))
    {Z : LocalizedCategory.{u, max z v, max z v} (K := K)} (f : ∀ j, Y j ⟶ Z)
    (hf : ∀ j, quasiEtale (f j)) :
    quasiEtale (Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan Y) f) := by
  let T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K :=
    fun j => localizedObjectEquiv.symm (Y j)
  let R := rightFractionCoproducts K J
  let D : localizationFunctor.obj (sigmaPresentation T) ⟶ Z :=
    Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan Y) f
  refine quasiEtale_of_forall_isLocalizedQuasiEtaleAt (S := sigmaPresentation T) D ?_
  rintro ⟨j, x⟩
  let e : localizationFunctor.obj (nonemptyReplacement (T j)) ≅
      localizationFunctor.obj (T j) :=
    Localization.isoOfHom localizationFunctor (quasiIsomorphisms (K := K)) _ (R.π_mem (T j))
  have hx : localizedSpaceFunctor.map e.hom x = x :=
    localizedSpaceFunctor_map_localizationFunctor_map_apply (nonemptyReplacementHom (T j)) x
  have h1 : (T j).IsLocalizedQuasiEtaleAt (f j) x :=
    isLocalizedQuasiEtaleAt_of_quasiEtale (S := T j) (hf j) x
  have h2 : (nonemptyReplacement (T j)).IsLocalizedQuasiEtaleAt (e.hom ≫ f j) x :=
    IsLocalizedQuasiEtaleAt.of_iso e (ψ := f j) (by rw [hx]; exact h1)
  have h3 : e.hom ≫ f j = localizationFunctor.map ((sigmaCofan T).inj j) ≫ D := by
    have hfac₀ : (e.inv ≫ localizationFunctor.map ((sigmaCofan T).inj j)) ≫ D = f j :=
      Cofan.IsColimit.fac (isColimitLocalizedSigmaCofan Y) f j
    have hfac : e.inv ≫ (localizationFunctor.map ((sigmaCofan T).inj j) ≫ D) = f j :=
      (Category.assoc _ _ _).symm.trans hfac₀
    exact ((Iso.inv_comp_eq e).mp hfac).symm
  rw [h3] at h2
  exact IsLocalizedQuasiEtaleAt.map_of_isDomainEmbedding ((sigmaCofan T).inj j)
    (isDomainEmbedding_sigmaCofan_inj T j) (isOpenMap_sigmaCofan_inj_baseMap T j) h2

/-- A morphism out of a disjoint union of analytic spaces whose restriction to every piece is
quasi-étale (resp. étale) is quasi-étale (resp. étale). -/
theorem sigmaDesc_quasiEtale_etale : SigmaDescStatement.{u, v, z} := by
  intro K _ _ _ J Y Z f
  exact ⟨quasiEtale_sigmaDesc Y f, etale_sigmaDesc Y f⟩

end Langlands.Analytic.SaturatedAtlasPresentation
