import Langlands.Geometry.Analytic.GroundFieldExtensionReindexNaturality
import Langlands.Geometry.Analytic.CompatibleStrongOriginalRestriction

/-! # The reverse saturation comparison with arbitrary original index equivalences -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K} {I J : Type v}

/-- The reverse comparison from the actual saturation to the original
presentation, with the original charts relabelled in the ambient universe. -/
def fromSaturationReindex (A : AffinoidAtlasPresentation.{u, v, w} K) {I : Type v}
    (e : I ≃ A.atlas.Index) : StrongHom A.saturatedPresentation (A.reindex e) :=
  let c : A.saturatedPresentation.atlas.Index ≃ A.saturationTarget.atlas.Index :=
    (Equiv.ulift : ULift.{w} A.atlas.localDomainFamily ≃ A.atlas.localDomainFamily).symm
  let d : I ≃ A.saturationSource.atlas.Index :=
    e.trans (Equiv.ulift : ULift.{v} A.atlas.Index ≃ A.atlas.Index).symm
  A.fromSaturation.reindex c d

theorem isQuasiIso_fromSaturationReindex (A : AffinoidAtlasPresentation.{u, v, w} K) {I : Type v}
    (e : I ≃ A.atlas.Index) : (A.fromSaturationReindex e).IsQuasiIso := by
  unfold fromSaturationReindex
  exact A.isQuasiIso_fromSaturation.reindex _ _

/-- This comparison is compatible because its source is saturated. -/
def compatibleFromSaturationReindex (A : AffinoidAtlasPresentation.{u, v, w} K) {I : Type v}
    (e : I ≃ A.atlas.Index) : CompatibleStrongHom A.saturatedPresentation (A.reindex e) :=
  CompatibleStrongHom.ofSaturated (A.fromSaturationReindex e) A.atlas.saturatedAtlas_hasAllLocalDomains

private theorem fromSaturationReindex_admissible (e : I ≃ A.atlas.Index) (i : I) :
    (A.compatibleFromSaturationReindex e).baseMap ''
      range (A.saturatedPresentation.atlas.chart (A.atlas.originalSaturatedIndex (e i))) ⊆
      range ((A.reindex e).atlas.chart i) := by
  change id '' range (A.atlas.saturatedAtlas.chart (A.atlas.originalSaturatedIndex (e i))) ⊆
    range (A.atlas.chart (e i))
  rw [image_id, A.atlas.saturatedAtlas_original_range]

private theorem fromSaturationReindex_pullback_heq (e : I ≃ A.atlas.Index) (i : I) :
    HEq ((A.compatibleFromSaturationReindex e).pullback
      (A.atlas.originalSaturatedIndex (e i)) i (fromSaturationReindex_admissible e i))
      (BoundedAlgHom.id K (A.atlas.algebra (e i))) := by
  let D := A.atlas.originalLocalDomain (e i)
  have h (U : LocalDomain A.atlas) (hU : U = D) (p : U ⟶ D) :
      HEq p.restriction (BoundedAlgHom.id K (A.atlas.algebra (e i))) := by
    subst U
    exact heq_of_eq (congrArg LocalDomain.Inclusion.restriction
      (@Subsingleton.elim (LocalDomain.Inclusion D D) inferInstance p (𝟙 D)))
  exact h _ (A.atlas.saturatedRepresentative_original (e i)) _

/-- The comparison transports whole compatible maps. At original chart
pairs the comparison maps are bounded identities after identifying algebras. -/
theorem compatibleFromSaturationReindex_natural (eA : I ≃ A.atlas.Index) (eB : J ≃ B.atlas.Index)
    (f : CompatibleStrongHom A B) :
    (CompatibleStrongHom.ofSaturated f.saturationExtension A.atlas.saturatedAtlas_hasAllLocalDomains).comp
        (B.compatibleFromSaturationReindex eB) =
      (A.compatibleFromSaturationReindex eA).comp (f.reindex eA eB) := by
  let F := CompatibleStrongHom.ofSaturated f.saturationExtension A.atlas.saturatedAtlas_hasAllLocalDomains
  let a := A.compatibleFromSaturationReindex eA
  let b := B.compatibleFromSaturationReindex eB
  let f' := f.reindex eA eB
  have hb : (F.comp b).baseMap = (a.comp f').baseMap := rfl
  refine CompatibleStrongHom.ext_of_pullback hb fun S => ?_
  let i := (A.atlas.saturatedRepresentative S).index
  obtain ⟨m, hm⟩ := eA.surjective i
  obtain ⟨j, hj⟩ := f.target_exists (eA m)
  obtain ⟨n, rfl⟩ := eB.surjective j
  let U := A.atlas.originalSaturatedIndex (eA m)
  let V := B.atlas.originalSaturatedIndex (eB n)
  have hSU : range (A.saturatedPresentation.atlas.chart S) ⊆
      range (A.saturatedPresentation.atlas.chart U) := by
    change range (A.saturatedPresentation.atlas.chart S) ⊆
      range (A.saturatedPresentation.atlas.chart (A.atlas.originalSaturatedIndex (eA m)))
    rw [hm]
    exact StrongHom.saturated_chart_subset_parent S
  have hF : F.baseMap '' range (A.saturatedPresentation.atlas.chart U) ⊆
      range (B.saturatedPresentation.atlas.chart V) :=
    f.toStrongHom.saturationExtension_original_admissible (eA m) (eB n) hj
  have ha := fromSaturationReindex_admissible eA m
  have hb' := fromSaturationReindex_admissible eB n
  have hu := F.toStrongHom.comp_admissible b.toStrongHom U V n hF hb'
  have hu' := a.toStrongHom.comp_admissible f'.toStrongHom U m n ha hj
  have hs := (image_mono hSU).trans hu
  have hs' := (image_mono hSU).trans hu'
  have hcomp : (F.comp b).pullback U n hu = (a.comp f').pullback U n hu' := by
    rw [CompatibleStrongHom.comp_pullback F b U V n hF hb' hu,
      CompatibleStrongHom.comp_pullback a f' U m n ha hj hu']
    have hl := BoundedAlgHom.comp_heq
      (A.atlas.saturatedAtlas_original_algebra (eA m)) (B.atlas.saturatedAtlas_original_algebra (eB n)) rfl
      (f.toStrongHom.saturationExtension_pullback_original f.coherent (eA m) (eB n) hj)
      (fromSaturationReindex_pullback_heq eB n)
    have hr := BoundedAlgHom.comp_heq (A.atlas.saturatedAtlas_original_algebra (eA m)) rfl rfl
      (fromSaturationReindex_pullback_heq eA m)
      (heq_of_eq (rfl : f'.pullback m n hj = f.pullback (eA m) (eB n) hj))
    exact eq_of_heq ((hl.trans (heq_of_eq (BoundedAlgHom.comp_id _))).trans
      (hr.trans (heq_of_eq (BoundedAlgHom.id_comp _))).symm)
  exact ⟨n, hs, ((F.comp b).toStrongHom.restriction_comp_pullback S U n hSU hs hu).symm.trans
    ((congrArg (fun φ => (A.saturatedPresentation.atlas.restriction S U hSU).comp φ) hcomp).trans
      ((a.comp f').toStrongHom.restriction_comp_pullback S U n hSU hs' hu'))⟩

end Langlands.Analytic.AffinoidAtlasPresentation
