import Langlands.Geometry.Analytic.CompatibleAtlasTransport
import Langlands.Geometry.Analytic.SaturatedStrongLocalization
import Mathlib.Topology.Category.TopCat.ULift

/-! # Functorial universe enlargement of the actual analytic presentations -/

noncomputable section

universe u v w z t

namespace Langlands.Analytic

open CategoryTheory Set AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {Y : Type z} [TopologicalSpace Y] (e : X ≃ₜ Y) {I : Type t} (c : I ≃ a.Index)

theorem HasAllLocalDomains.transportReindex (ha : a.HasAllLocalDomains) :
    ((a.transport e).reindex c).HasAllLocalDomains := by
  let b := (a.transport e).reindex c
  change b.localDomainFamily = range (fun i => range (b.chart i))
  apply Subset.antisymm
  · rintro _ ⟨U, rfl⟩
    let U' := LocalDomain.ofReindex (a.transport e) c U
    let V := LocalDomain.ofTransport a e U'
    obtain ⟨j, hj⟩ := ha.exists_chart V
    obtain ⟨i, rfl⟩ := c.surjective j
    refine ⟨i, ?_⟩
    change range (a.transportChart e (c i)) = U.locus
    rw [a.range_transportChart, hj]
    change e '' (a.chart V.index '' V.domain.locus) = U.locus
    rw [image_image]
    rfl
  · rintro _ ⟨i, rfl⟩
    exact ⟨b.originalLocalDomain i, b.originalLocalDomain_locus i⟩

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

/-- Lift the two independent universes, without changing any presented algebra. -/
def universeLift (A : AffinoidAtlasPresentation.{u, v, w} K) :
    AffinoidAtlasPresentation.{u, max v z, max w t} K :=
  A.transportReindex (Homeomorph.ulift.{z}.symm) (Equiv.ulift : ULift.{t} A.atlas.Index ≃ _)

namespace CompatibleStrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

def universeLift (f : CompatibleStrongHom A B) :
    CompatibleStrongHom (AffinoidAtlasPresentation.universeLift.{u, v, w, z, t} A)
      (AffinoidAtlasPresentation.universeLift.{u, v, w, z, t} B) :=
  f.transportReindex Homeomorph.ulift.symm Homeomorph.ulift.symm Equiv.ulift Equiv.ulift

private theorem universeLift_isQuasiIso (f : CompatibleStrongHom A B) (h : f.toStrongHom.IsQuasiIso) :
    (universeLift.{u, v, w, z, t} f).toStrongHom.IsQuasiIso :=
  h.transportReindex Homeomorph.ulift.symm Homeomorph.ulift.symm Equiv.ulift Equiv.ulift

@[simp]
theorem universeLift_baseMap (f : CompatibleStrongHom A B) (x : ULift.{z} A.space) :
    (universeLift.{u, v, w, z, t} f).baseMap x = ULift.up (f.baseMap x.down) := rfl

private theorem universeLift_id (A : AffinoidAtlasPresentation.{u, v, w} K) :
    universeLift.{u, v, w, z, t} (id A) = id (A.universeLift) := by
  refine ext_of_pullback (ContinuousMap.ext fun x => ?_) ?_
  · exact ULift.up_down x
  intro (i : ULift.{t} A.atlas.Index)
  have h : (universeLift.{u, v, w, z, t} (id A)).baseMap ''
      range ((AffinoidAtlasPresentation.universeLift.{u, v, w, z, t} A).atlas.chart i) ⊆
        range ((AffinoidAtlasPresentation.universeLift.{u, v, w, z, t} A).atlas.chart i) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  refine ⟨i, h, ?_⟩
  change A.atlas.restriction i.down i.down _ = A.atlas.restriction i.down i.down _
  rfl

private theorem universeLift_comp (f : CompatibleStrongHom A B) (g : CompatibleStrongHom B C) :
    universeLift.{u, v, w, z, t} (f.comp g) = (universeLift.{u, v, w, z, t} f).comp
      (universeLift.{u, v, w, z, t} g) := by
  refine ext_of_pullback rfl ?_
  intro (i : ULift.{t} A.atlas.Index)
  let F := universeLift.{u, v, w, z, t} f
  let G := universeLift.{u, v, w, z, t} g
  obtain ⟨j, hj⟩ := F.target_exists i
  obtain ⟨k, hk⟩ := G.target_exists j
  have hg := F.toStrongHom.comp_admissible G.toStrongHom i j k hj hk
  have hF := (StrongHom.transportedBaseMap_admissible_iff Homeomorph.ulift.symm
    Homeomorph.ulift.symm Equiv.ulift Equiv.ulift f.toStrongHom i j).1 hj
  have hG := (StrongHom.transportedBaseMap_admissible_iff Homeomorph.ulift.symm
    Homeomorph.ulift.symm Equiv.ulift Equiv.ulift g.toStrongHom j k).1 hk
  refine ⟨k, hg, ?_⟩
  have hcomp := CompatibleStrongHom.comp_pullback F G i j k hj hk hg
  refine Eq.trans ?_ hcomp.symm
  have hfg := f.toStrongHom.comp_admissible g.toStrongHom i.down j.down k.down hF hG
  change (f.comp g).pullback i.down k.down hfg =
    (f.pullback i.down j.down hF).comp (g.pullback j.down k.down hG)
  exact CompatibleStrongHom.comp_pullback f g i.down j.down k.down hF hG hfg

end CompatibleStrongHom
end AffinoidAtlasPresentation

namespace SaturatedAtlasPresentation

/-- The universe lift of an arbitrary saturated presentation is saturated. -/
def universeLift (A : SaturatedAtlasPresentation.{u, v, w} K) :
    SaturatedAtlasPresentation.{u, max v z, max w t} K where
  presentation := AffinoidAtlasPresentation.universeLift.{u, v, w, z, t} A.presentation
  hasAllLocalDomains := A.hasAllLocalDomains.transportReindex _ _

/-- The lift retains the entire bounded data of every saturated strong map. -/
def universeLiftFunctor : SaturatedAtlasPresentation.{u, v, w} K ⥤
    SaturatedAtlasPresentation.{u, max v z, max w t} K where
  obj := universeLift
  map f := (CompatibleStrongHom.universeLift.{u, v, w, z, t} (compatibleFunctor.map f)).toStrongHom
  map_id A := congrArg CompatibleStrongHom.toStrongHom (CompatibleStrongHom.universeLift_id A.presentation)
  map_comp f g := congrArg CompatibleStrongHom.toStrongHom
    (CompatibleStrongHom.universeLift_comp (compatibleFunctor.map f) (compatibleFunctor.map g))

theorem universeLiftFunctor_isQuasiIso {A B : SaturatedAtlasPresentation.{u, v, w} K}
    (f : A ⟶ B) (h : f.IsQuasiIso) :
    ((universeLiftFunctor.{u, v, w, z, t} (K := K)).map f).IsQuasiIso :=
  CompatibleStrongHom.universeLift_isQuasiIso (compatibleFunctor.map f) h

private theorem universeLiftFunctor_inverts :
    (quasiIsomorphisms (K := K) : MorphismProperty (SaturatedAtlasPresentation.{u, v, w} K)).IsInvertedBy
        (universeLiftFunctor.{u, v, w, z, t} ⋙ localizationFunctor) := by
  intro A B f hf
  let e := localizedQuasiIso ((universeLiftFunctor.{u, v, w, z, t} (K := K)).map f)
    (universeLiftFunctor_isQuasiIso f hf)
  change IsIso e.hom
  infer_instance

/-- Functorial enlargement on the actual localized analytic category. -/
def localizedUniverseLift : LocalizedCategory.{u, v, w} (K := K) ⥤
    LocalizedCategory.{u, max v z, max w t} (K := K) :=
  descend (universeLiftFunctor ⋙ localizationFunctor) universeLiftFunctor_inverts

@[simp]
theorem localizationFunctor_localizedUniverseLift :
    localizationFunctor (K := K) ⋙ localizedUniverseLift.{u, v, w, z, t} =
      universeLiftFunctor ⋙ localizationFunctor := localizationFunctor_descend _ _

@[simp]
theorem localizedUniverseLift_obj (A : SaturatedAtlasPresentation.{u, v, w} K) :
    (localizedUniverseLift.{u, v, w, z, t} (K := K)).obj (localizationFunctor.obj A) =
      localizationFunctor.obj (universeLift.{u, v, w, z, t} A) := rfl

@[simp]
theorem localizedUniverseLift_map {A B : SaturatedAtlasPresentation.{u, v, w} K} (f : A ⟶ B) :
    (localizedUniverseLift.{u, v, w, z, t} (K := K)).map (localizationFunctor.map f) =
      localizationFunctor.map ((universeLiftFunctor.{u, v, w, z, t}).map f) :=
  Functor.congr_hom localizationFunctor_localizedUniverseLift f

/-- On the original saturated category, the ambient space is exactly Mathlib's
lifted topological space and each map is the corresponding lifted continuous map. -/
theorem universeLiftFunctor_spaceFunctor : universeLiftFunctor.{u, v, w, z, t} (K := K) ⋙
    spaceFunctor = spaceFunctor ⋙ TopCat.uliftFunctor.{z, v} := rfl

/-- The same equation holds after localization, including for formal inverses. -/
theorem localizedUniverseLift_spaceFunctor : localizedUniverseLift.{u, v, w, z, t} (K := K) ⋙
    localizedSpaceFunctor = localizedSpaceFunctor ⋙ TopCat.uliftFunctor.{z, v} := by
  let F := (spaceFunctor : SaturatedAtlasPresentation.{u, v, w} K ⥤ _) ⋙
    TopCat.uliftFunctor.{z, v}
  have hF : (quasiIsomorphisms (K := K) :
      MorphismProperty (SaturatedAtlasPresentation.{u, v, w} K)).IsInvertedBy F := by
    intro A B f hf
    have : IsIso (spaceFunctor.map f) := spaceFunctor_inverts_quasiIsomorphisms f hf
    change IsIso ((TopCat.uliftFunctor.{z, v}).map (spaceFunctor.map f))
    infer_instance
  refine (descend_unique F hF _ ?_).trans (descend_unique F hF _ ?_).symm
  · calc
      _ = (localizationFunctor ⋙ localizedUniverseLift.{u, v, w, z, t}) ⋙
            localizedSpaceFunctor := rfl
      _ = (universeLiftFunctor.{u, v, w, z, t} ⋙ localizationFunctor) ⋙
            localizedSpaceFunctor := by rw [localizationFunctor_localizedUniverseLift]
      _ = universeLiftFunctor.{u, v, w, z, t} ⋙ spaceFunctor := by
        rw [Functor.assoc, localizationFunctor_localizedSpaceFunctor]
      _ = F := universeLiftFunctor_spaceFunctor
  · calc
      _ = (localizationFunctor ⋙ localizedSpaceFunctor) ⋙ TopCat.uliftFunctor.{z, v} := rfl
      _ = F := by rw [localizationFunctor_localizedSpaceFunctor]

end SaturatedAtlasPresentation
end Langlands.Analytic
