import Langlands.Geometry.Analytic.EquivariantEtaleBaseChangeMorphismStatement

/-! # Equivariant étale base change is a morphism of sites -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation.SpaceWithOperators

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {Y X : SpaceWithOperators.{u, v, v, z} K}

/-- Naturality of the analytic first projections is a pullback square. -/
theorem etalePullbackMap_isPullback (f : Y ⟶ X) {U V : EquivariantEtaleSite X.space}
    (g : U ⟶ V) :
    IsPullback (GSpace.forget.map ((etalePullbackFunctor f).map g).left)
      (GSpace.forget.map (etalePullbackProjection f U))
      (GSpace.forget.map (etalePullbackProjection f V))
      ((GSpace.forget (G := X.group.carrier)).map g.left) := by
  let F := etalePullbackFunctor f
  let H := GSpace.forget (K := K) (G := Y.group.carrier)
  let G := GSpace.forget (K := K) (G := X.group.carrier)
  have hp : H.map (F.map g).left ≫ H.map (etalePullbackProjection f V) =
      H.map (etalePullbackProjection f U) ≫ G.map g.left := by
    rw [← H.map_comp]
    change H.map ((F.map g).left ≫ etalePullbackProjection f V) =
      H.map (etalePullbackProjection f U) ≫ H.map ((GSpace.res f.groupHom).map g.left)
    rw [← H.map_comp]
    congr 1
    simp only [F, etalePullbackFunctor, Functor.comp_map, MorphismProperty.Over.pullback_map_left,
      EquivariantEtaleSite.res_map_left, etalePullbackProjection]
    have hV : HasPullback ((EquivariantEtaleSite.res f.groupHom).obj V).hom (restrictedHom f) :=
      MorphismProperty.hasPullback (P := GSpace.etale) _ ((EquivariantEtaleSite.res f.groupHom).obj V).prop
    exact @pullback.lift_fst _ _ _ _ _ _ _ _ hV _ _ _
  have h₁ : H.map (F.map g).left ≫ H.map (F.obj V).hom = H.map (F.obj U).hom := by
    rw [← H.map_comp, MorphismProperty.Over.w]
  have h₂ : G.map g.left ≫ G.map V.hom = G.map U.hom := by
    rw [← G.map_comp, MorphismProperty.Over.w]
  refine IsPullback.of_right ?_ hp (isPullback_etalePullbackFunctor f V).flip
  rw [h₁]
  change IsPullback (H.map (F.obj U).hom) (H.map (etalePullbackProjection f U)) f.hom
    (G.map g.left ≫ G.map V.hom)
  exact (congrArg (IsPullback (H.map (F.obj U).hom) (H.map (etalePullbackProjection f U)) f.hom)
    h₂).mpr (isPullback_etalePullbackFunctor f U).flip

/-- Étale base change by a morphism with operators is representably flat and
continuous for the equivariant étale Grothendieck topologies. -/
theorem etalePullbackFunctor_morphismOfSites (f : Y ⟶ X) :
    RepresentablyFlat (etalePullbackFunctor f) ∧
      (etalePullbackFunctor f).IsContinuous (equivariantEtaleTopology X.space)
        (equivariantEtaleTopology Y.space) := by
  let F := etalePullbackFunctor f
  let H := GSpace.forget (K := K) (G := Y.group.carrier)
  refine GSpace.representablyFlat_and_isContinuous_of_isPullback_forget F
    (fun _ _ _ g h => EquivariantEtaleSite.exists_analyticPullback g h) ?_ ?_
    (equivariantEtalePrecoverage X.space) (equivariantEtalePrecoverage Y.space) ?_
  · intro P U V W p q g h sq
    have hc := (GSpace.isPullback_of_isPullback_forget (P := GSpace.etale) sq).w
    have hcomp : H.map (F.map p).left ≫ H.map (F.map g).left =
        H.map (F.map q).left ≫ H.map (F.map h).left := by
      simp only [← H.map_comp, ← MorphismProperty.Comma.comp_left, ← F.map_comp, hc]
    refine IsPullback.of_bot ?_ hcomp (etalePullbackMap_isPullback f h)
    rw [(etalePullbackMap_isPullback f q).w, (etalePullbackMap_isPullback f g).w]
    exact (etalePullbackMap_isPullback f p).paste_vert sq
  · intro U hU
    let U' := (EquivariantEtaleSite.res f.groupHom).obj U
    have : IsIso U'.hom := (GSpace.res f.groupHom).map_isIso U.hom
    exact (IsPullback.of_hasPullback U'.hom (restrictedHom f)).isIso_snd_of_isIso
  · intro U R hR
    rw [mem_equivariantEtalePrecoverage_iff] at hR ⊢
    intro x
    let y := localizedSpaceFunctor.map (H.map (etalePullbackProjection f U)) x
    obtain ⟨V, g, hg, z, hz⟩ := hR y
    obtain ⟨w, -, hw⟩ := exists_point_of_isPullback_of_etale
      (etalePullbackMap_isPullback f g).flip (EquivariantEtaleSite.etale_map_left g) z x hz
    exact ⟨F.obj V, F.map g, Presieve.map_map hg, w, hw⟩

/-- The equivariant étale base-change morphism for all complete ground fields. -/
theorem equivariantEtaleBaseChangeMorphism :
    EquivariantEtaleBaseChangeMorphismStatement.{u, v, z} :=
  fun _ _ _ _ _ _ f => etalePullbackFunctor_morphismOfSites f

end Langlands.Analytic.SaturatedAtlasPresentation.SpaceWithOperators
