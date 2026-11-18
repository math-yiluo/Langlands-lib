import Langlands.Geometry.Analytic.AnalyticImmersion
import Langlands.Geometry.Analytic.FieldPointDomains

/-! # Field-valued point lifting along analytic open immersions -/

noncomputable section

universe u v w uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]

set_option backward.isDefEq.respectTransparency false in
/-- Full field-valued points restrict to every containing analytic domain. -/
theorem exists_fieldPoint_lift_domainι
    {Y : LocalizedCategory.{u, v, w} (K := K)}
    (D : (presentationOf Y).AnalyticDomain)
    (p : (localizedFieldPointFunctor L).obj Y)
    (hp : ((localizedFieldPointProjection L).app Y p).down ∈ D.carrier) :
    ∃ q : (localizedFieldPointFunctor L).obj (domainObj Y D),
      (localizedFieldPointFunctor L).map (domainι Y D) q = p := by
  obtain ⟨S, rfl⟩ := localizedObjectEquiv.surjective Y
  let q := AffinoidAtlasPresentation.FieldPoint.restrictOriginalDomain p D hp
  refine ⟨q, ?_⟩
  change q.map (S.domainInclusion D) (S.domain D).hasAllLocalDomains = p
  exact fieldPoint_map_restrictOriginalDomain D p hp

/-- An analytic open immersion lifts a full field-valued point whenever
its ordinary point belongs to the image. -/
def OpenImmersionFieldPointLiftingStatement : Prop :=
  ∀ {U V : LocalizedCategory.{u, v, w} (K := K)} (f : U ⟶ V),
    openImmersion f → ∀ p : (localizedFieldPointFunctor L).obj V,
      ((localizedFieldPointProjection L).app V p).down ∈
          Set.range (localizedSpaceFunctor.map f) →
        ∃ q : (localizedFieldPointFunctor L).obj U,
          (localizedFieldPointFunctor L).map f q = p

set_option backward.isDefEq.respectTransparency false in
/-- Actual domain restriction and the analytic isomorphism in an open
immersion give the full field-valued point lift. -/
theorem openImmersionFieldPointLifting :
    OpenImmersionFieldPointLiftingStatement (K := K) (L := L) := by
  intro U V f hf p hp
  obtain ⟨N, hN, e, rfl⟩ := hf
  obtain ⟨z, hz⟩ := hp
  have hmem : ((localizedFieldPointProjection L).app V p).down ∈ N := by
    rw [← hz, Functor.map_comp, TopCat.comp_app, domainι_apply]
    exact (localizedSpaceFunctor.map e.hom z).property
  obtain ⟨q, hq⟩ := exists_fieldPoint_lift_domainι ((presentationOf V).openDomain N hN) p hmem
  refine ⟨(localizedFieldPointFunctor L).map e.inv q, ?_⟩
  rw [← Functor.map_comp_apply, Iso.inv_hom_id_assoc]
  exact hq

set_option backward.isDefEq.respectTransparency false in
/-- Projection to ordinary points commutes with every analytic morphism. -/
theorem localizedFieldPointProjection_map_down
    {U V : LocalizedCategory.{u, v, w} (K := K)} (f : U ⟶ V)
    (q : (localizedFieldPointFunctor L).obj U) :
    ((localizedFieldPointProjection L).app V ((localizedFieldPointFunctor L).map f q)).down =
      localizedSpaceFunctor.map f (((localizedFieldPointProjection L).app U q).down) := by
  have h := congrArg (fun k => k q) ((localizedFieldPointProjection L).naturality f)
  exact congrArg ULift.down h

set_option backward.isDefEq.respectTransparency false in
/-- The full lift through an open immersion has any prescribed ordinary
source point above the given target field point. -/
theorem exists_fieldPoint_lift_at_openImmersion
    {U V : LocalizedCategory.{u, v, w} (K := K)} (f : U ⟶ V) (hf : openImmersion f)
    (p : (localizedFieldPointFunctor L).obj V) (x : localizedSpaceFunctor.obj U)
    (hx : localizedSpaceFunctor.map f x =
      ((localizedFieldPointProjection L).app V p).down) :
    ∃ q : (localizedFieldPointFunctor L).obj U,
      ((localizedFieldPointProjection L).app U q).down = x ∧
        (localizedFieldPointFunctor L).map f q = p := by
  obtain ⟨q, hq⟩ := openImmersionFieldPointLifting f hf p ⟨x, hx⟩
  refine ⟨q, ?_, hq⟩
  have hn := localizedFieldPointProjection_map_down f q
  rw [hq] at hn
  exact hf.isOpenEmbedding.injective (hn.symm.trans hx.symm)

end Langlands.Analytic.SaturatedAtlasPresentation
