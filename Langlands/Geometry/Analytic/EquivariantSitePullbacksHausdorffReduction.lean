import Langlands.Geometry.Analytic.QuasiEtaleHausdorffStabilityStatement
import Langlands.Geometry.Analytic.EquivariantSitePullbacksReduction

/-! # Equivariant quasi-étale fibre products from Hausdorff quasi-étale stability -/

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- The three Hausdorff stability statements give the fibre products of `Qét(X(G))`:
the spaces of `G`-spaces are Hausdorff, and so is the pullback vertex. -/
theorem equivariantQuasiEtalePullbacksHausdorffReduction :
    EquivariantQuasiEtalePullbacksHausdorffReductionStatement.{u, v, z} := by
  intro hComp hBase hOver K _ _ _ G _ _ X U₁ U₂ U₃ f₁ f₂
  have hU₁ : T2Space (localizedSpaceFunctor.obj (GSpace.forget.obj U₁.left)) := U₁.left.2.1
  have hU₂ : T2Space (localizedSpaceFunctor.obj (GSpace.forget.obj U₂.left)) := U₂.left.2.1
  have hU₃ : T2Space (localizedSpaceFunctor.obj (GSpace.forget.obj U₃.left)) := U₃.left.2.1
  have hw : GSpace.forget.map f₁.left ≫ GSpace.forget.map U₃.hom =
      GSpace.forget.map U₁.hom := by
    rw [← Functor.map_comp, MorphismProperty.Over.w f₁]
  have hf : quasiEtale (GSpace.forget.map f₁.left) :=
    hOver K _ _ hU₃ U₃.prop (hw.symm ▸ U₁.prop)
  obtain ⟨P, p, q, hpq⟩ := exists_localizedPullback_of_quasiEtale
    (GSpace.forget.map f₁.left) (GSpace.forget.map f₂.left) hf
  have hq : quasiEtale q := hBase K hpq hU₁ hf
  have hP : T2Space (localizedSpaceFunctor.obj P) :=
    (hasCompactPairPreimages_of_quasiEtale hpq hf).1
  exact exists_equivariantSitePullback_of_isPullback f₁ f₂ hpq hf
    (hComp K _ _ hP hU₂ hq U₂.prop)

end Langlands.Analytic.SaturatedAtlasPresentation
