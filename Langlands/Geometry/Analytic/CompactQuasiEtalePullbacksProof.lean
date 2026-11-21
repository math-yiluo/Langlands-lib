import Langlands.Geometry.Analytic.CompactDiagonalPreimage
import Langlands.Geometry.Analytic.CompactQuasiEtaleDiagonal
import Langlands.Geometry.Analytic.CompactQuasiEtalePullbacks
import Langlands.Geometry.Analytic.QuasiEtaleCommonProduct

/-! # Compact pullbacks in the quasi-étale site -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Cut the product over the ambient base by the diagonal of the compact
intermediate object. -/
theorem compactQuasiEtalePullbacks :
    CompactQuasiEtalePullbacksStatement.{u, v} (K := K) := by
  intro X B U V f g hB hU hV
  let p := localizedQuasiEtalePullback U.hom V.hom U.prop
  let q := localizedQuasiEtalePullback B.hom B.hom B.prop
  have hp := IsPullback.of_isLimit p.2
  have hq := IsPullback.of_isLimit q.2
  have hp' : IsPullback p.1.fst p.1.snd (f.left ≫ B.hom) (g.left ≫ B.hom) := by
    simpa only [MorphismProperty.Over.w] using hp
  have hf : quasiEtale (f.left ≫ B.hom) := (MorphismProperty.Over.w f).symm ▸ U.prop
  let D := compactRelativePullbackOfDiagonal hp' hq hf B.prop hU hV hB
    (compactQuasiEtaleDiagonalDomain hq hB B.prop)
  let i := domainι p.1.pt D.domain
  let : T2Space (localizedSpaceFunctor.obj U.left) := hU.2
  let : T2Space (localizedSpaceFunctor.obj V.left) := hV.2
  have hUloc := hasLocalDomainEtaleFactorizations_of_quasiEtale (U := U.left) U.prop
  have hVloc := hasLocalDomainEtaleFactorizations_of_quasiEtale (U := V.left) V.prop
  have hW := ((hUloc.of_isPullback_common hVloc hp).domainι_comp D.domain).quasiEtale
  let W := MorphismProperty.Over.mk ⊤ (i ≫ (p.1.snd ≫ V.hom)) hW
  let a : W ⟶ U := MorphismProperty.Over.homMk (i ≫ p.1.fst) (by
    change (i ≫ p.1.fst) ≫ U.hom = i ≫ (p.1.snd ≫ V.hom)
    rw [Category.assoc, hp.w])
  let b : W ⟶ V := MorphismProperty.Over.homMk (i ≫ p.1.snd) (Category.assoc _ _ _)
  exact ⟨PullbackCone.mk a b (MorphismProperty.Over.Hom.ext D.isPullback.w),
    D.compact, D.isPullback⟩

end Langlands.Analytic.SaturatedAtlasPresentation
