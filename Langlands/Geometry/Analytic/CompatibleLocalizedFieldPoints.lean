import Langlands.Geometry.Analytic.FibreProductPoints
import Langlands.Geometry.Analytic.FibreProductSmallSquare
import Langlands.Geometry.Analytic.FieldPointChartExtension
import Langlands.Geometry.Analytic.FiniteChartFieldPointPullbacks
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCompletedResidueProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.PointAmalgamationProof
import Langlands.Geometry.Analytic.SaturatedRightFractionComposition
import Langlands.Geometry.Analytic.ValuedField.CompleteAlgebraicClosure

/-! # Compatible field points above a pair of ordinary points -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Set AffinoidAtlasPresentation PresentedAffinoidAlgebra ValuedField

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem exists_compatible_fieldPoints_of_strong
    {A B C : SaturatedAtlasPresentation.{u, v, v} K} (f : A ⟶ C) (g : B ⟶ C)
    (x : A.presentation.space) (y : B.presentation.space) (hxy : f.baseMap x = g.baseMap y) :
    ∃ (L : Type u) (_ : NormedField L) (_ : IsUltrametricDist L) (_ : CompleteSpace L)
      (_ : IsAlgClosed L) (_ : NormedAlgebra K L)
      (a : FieldPoint L A.presentation) (b : FieldPoint L B.presentation),
      a.point = x ∧ b.point = y ∧ a.map f A.hasAllLocalDomains = b.map g B.hasAllLocalDomains := by
  let F := geometricCompatibleMap f
  let G := geometricCompatibleMap g
  obtain ⟨p, ⟨s, hs⟩, ⟨t, ht⟩⟩ := FibreProduct.exists_pair_of_compatible_points F G
    A.hasAllLocalDomains B.hasAllLocalDomains x y hxy
  let k := FibreProduct.base F G p
  have hk := FibreProduct.isCommonBase_base F G p
  let α := FibreProduct.leftBase F G p
  let β := FibreProduct.rightBase F G p
  have hst : BanachSpectrum.comap α.toBoundedRingHom s =
      BanachSpectrum.comap β.toBoundedRingHom t := by
    apply (C.presentation.atlas.isEmbedding_chart k).injective
    change C.presentation.atlas.chart k
        (BanachSpectrum.comap (F.pullback p.1.1 k hk.1).toBoundedRingHom s) =
      C.presentation.atlas.chart k
        (BanachSpectrum.comap (G.pullback p.1.2 k hk.2).toBoundedRingHom t)
    rw [F.chart_comm, G.chart_comm, hs, ht]
    exact hxy
  obtain ⟨H, _, _, _, _, φ, ψ, hφψ, hφ, hψ⟩ :=
    pointAmalgamation K _ _ _ α β s t hst
  let L := CompleteAlgebraicClosure H
  let ι : K →+* L := (algebraMap H L).comp (algebraMap K H)
  let : NormedAlgebra K L := {
    __ := ι.toAlgebra
    norm_smul_le a z := by
      change ‖algebraMap H L (algebraMap K H a) * z‖ ≤ ‖a‖ * ‖z‖
      rw [norm_mul, norm_algebraMap', norm_algebraMap']
  }
  let j : H →ₐ[K] L := { toRingHom := algebraMap H L, commutes' := fun _ => rfl }
  let χ := j.comp φ.toAlgHom
  let η := j.comp ψ.toAlgHom
  have hχ : IsChartCharacter x p.1.1 χ := by
    refine ⟨s, hs, fun a => ?_⟩
    change ‖algebraMap H L (φ a)‖ = s a
    rw [norm_algebraMap', hφ]
  have hη : IsChartCharacter y p.1.2 η := by
    refine ⟨t, ht, fun a => ?_⟩
    change ‖algebraMap H L (ψ a)‖ = t a
    rw [norm_algebraMap', hψ]
  obtain ⟨a, ⟨ha, hai, hEvalA⟩, -⟩ :=
    FieldPoint.existsUnique_of_chartCharacter domainCompletedResidueSurjectivity x p.1.1 χ hχ
  obtain ⟨b, ⟨hb, hbi, hEvalB⟩, -⟩ :=
    FieldPoint.existsUnique_of_chartCharacter domainCompletedResidueSurjectivity y p.1.2 η hη
  have hpoint : (a.map f A.hasAllLocalDomains).point = (b.map g B.hasAllLocalDomains).point :=
    (congrArg f.baseMap ha).trans (hxy.trans (congrArg g.baseMap hb).symm)
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    a, b, ha, hb, ?_⟩
  refine FieldPoint.eq_of_eval_eq domainCompletedResidueSurjectivity hpoint k
    (hk.1 ⟨a.point, hai, rfl⟩) (hk.2 ⟨b.point, hbi, rfl⟩) ?_
  erw [a.map_eval f A.hasAllLocalDomains k _ p.1.1 hai hk.1,
    b.map_eval g B.hasAllLocalDomains k _ p.1.2 hbi hk.2, hEvalA, hEvalB]
  ext z
  exact congrArg (algebraMap H L)
    (congrArg (fun q : BoundedAlgHom K (C.presentation.atlas.algebra k) H => q z) hφψ)

/-- A compatible ordinary pair of points lifts to full field points over
a common complete algebraically closed extension, with equal full base images. -/
theorem exists_compatible_localizedFieldPoints
    {A B C : LocalizedCategory.{u, v, v} (K := K)} (f : A ⟶ C) (g : B ⟶ C)
    (x : localizedSpaceFunctor.obj A) (y : localizedSpaceFunctor.obj B)
    (hxy : localizedSpaceFunctor.map f x = localizedSpaceFunctor.map g y) :
    ∃ (L : Type u) (_ : NormedField L) (_ : IsUltrametricDist L) (_ : CompleteSpace L)
      (_ : IsAlgClosed L) (_ : NormedAlgebra K L)
      (a : (localizedFieldPointFunctor L).obj A) (b : (localizedFieldPointFunctor L).obj B),
      ((localizedFieldPointProjection L).app A a).down = x ∧
        ((localizedFieldPointProjection L).app B b).down = y ∧
        (localizedFieldPointFunctor L).map f a = (localizedFieldPointFunctor L).map g b := by
  obtain ⟨A₀, rfl⟩ := localizedObjectEquiv.surjective A
  obtain ⟨B₀, rfl⟩ := localizedObjectEquiv.surjective B
  obtain ⟨C₀, rfl⟩ := localizedObjectEquiv.surjective C
  simp only [localizedObjectEquiv_apply] at *
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction f
  obtain ⟨ψ, rfl⟩ := exists_localizedRightFraction g
  have hxy' : φ.f.baseMap (φ.hs.inverseBaseMap x) = ψ.f.baseMap (ψ.hs.inverseBaseMap y) := by
    rw [localizedSpaceFunctor_map_rightFraction, localizedSpaceFunctor_map_rightFraction] at hxy
    exact hxy
  obtain ⟨L, _, _, _, _, _, a, b, ha, hb, hab⟩ :=
    exists_compatible_fieldPoints_of_strong φ.f ψ.f _ _ hxy'
  let F := localizedFieldPointFunctor (K := K) L
  let a' : F.obj (localizationFunctor.obj φ.X') := a
  let b' : F.obj (localizationFunctor.obj ψ.X') := b
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    F.map (localizationFunctor.map φ.s) a', F.map (localizationFunctor.map ψ.s) b', ?_, ?_, ?_⟩
  · change φ.s.baseMap a.point = x
    exact (congrArg φ.s.baseMap ha).trans (φ.hs.baseMap_inverseBaseMap x)
  · change ψ.s.baseMap b.point = y
    exact (congrArg ψ.s.baseMap hb).trans (ψ.hs.baseMap_inverseBaseMap y)
  · change F.map (localizedRightFraction φ) (F.map (localizationFunctor.map φ.s) a') =
      F.map (localizedRightFraction ψ) (F.map (localizationFunctor.map ψ.s) b')
    rw [← F.map_comp_apply, ← F.map_comp_apply,
      localizationFunctor_map_s_comp_localizedRightFraction,
      localizationFunctor_map_s_comp_localizedRightFraction]
    exact hab

end Langlands.Analytic.SaturatedAtlasPresentation
