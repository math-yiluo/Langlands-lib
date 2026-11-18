import Langlands.Geometry.Analytic.CommonPointField.Transport
import Langlands.Geometry.Analytic.FieldValuedPoints

/-! # Isometric change of value field for full analytic points -/

noncomputable section

universe u v w uL uM

namespace Langlands.Analytic

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]

namespace AffinoidAtlasPresentation.FieldPoint

variable {A : AffinoidAtlasPresentation.{u, v, w} K}

/-- Postcompose every chart evaluation with a norm-preserving algebra map. -/
def mapValue {M : Type uM} [NormedField M] [NormedAlgebra K M]
    (p : FieldPoint L A) (f : L →ₐ[K] M) (hf : ∀ a, ‖f a‖ = ‖a‖) :
    FieldPoint M A :=
  p.mapField f ((AddMonoidHomClass.isometry_iff_norm f).2 hf)

/-- Over the underlying point of a full base-field point, the only full
extension-valued point is its scalar image. -/
theorem eq_mapValue_of_point_eq (p : FieldPoint K A) (q : FieldPoint L A)
    (hq : q.point = p.point) :
    q = p.mapValue (Algebra.ofId K L) (norm_algebraMap' L) := by
  apply FieldPoint.ext' hq
  intro i hi hj
  obtain ⟨s, hs, hn⟩ := p.isChartPoint i hj
  obtain ⟨t, ht, hm⟩ := q.isChartPoint i hi
  have hts : t = s := (A.atlas.isEmbedding_chart i).injective (ht.trans (hq.trans hs.symm))
  subst t
  ext a
  let b := a - algebraMap K (A.atlas.algebra i) (p.eval i hj a)
  have hb : p.eval i hj b = 0 := by
    dsimp only [b]
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  have hz : q.eval i hi b = 0 :=
    norm_eq_zero.mp ((hm b).trans ((hn b).symm.trans (by rw [hb, norm_zero])))
  change q.eval i hi a = algebraMap K L (p.eval i hj a)
  dsimp only [b] at hz
  rwa [map_sub, AlgHom.commutes, sub_eq_zero] at hz

end AffinoidAtlasPresentation.FieldPoint

namespace SaturatedAtlasPresentation

open AffinoidAtlasPresentation

/-- The underlying-point maps commute with every localized morphism after
removing the universe lift. -/
theorem localizedFieldPointProjection_down_naturality
    {X Y : LocalizedCategory.{u, v, w} (K := K)} (f : X ⟶ Y)
    (q : (localizedFieldPointFunctor L).obj X) :
    ((localizedFieldPointProjection L).app Y ((localizedFieldPointFunctor L).map f q)).down =
      localizedSpaceFunctor.map f (((localizedFieldPointProjection L).app X q).down) :=
  congrArg (fun k => (k q).down) ((localizedFieldPointProjection L).naturality f)

/-- The fiber of the extension-valued projection over the underlying point
of a full base-field point has at most one element. -/
theorem localizedFieldPoint_eq_of_projection_eq_at_baseFieldPoint
    (Y : LocalizedCategory.{u, v, w} (K := K))
    (p : (localizedFieldPointFunctor K).obj Y)
    (q r : (localizedFieldPointFunctor L).obj Y)
    (hq : ((localizedFieldPointProjection L).app Y q).down =
      ((localizedFieldPointProjection K).app Y p).down)
    (hr : ((localizedFieldPointProjection L).app Y r).down =
      ((localizedFieldPointProjection K).app Y p).down) :
    q = r := by
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective Y
  exact (FieldPoint.eq_mapValue_of_point_eq p q hq).trans
    (FieldPoint.eq_mapValue_of_point_eq p r hr).symm

end SaturatedAtlasPresentation

end Langlands.Analytic
