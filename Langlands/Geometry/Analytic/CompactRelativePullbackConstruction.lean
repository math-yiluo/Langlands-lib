import Langlands.Geometry.Analytic.CompactDiagonalPreimage
import Langlands.Geometry.Analytic.CompactEquivariantPullbacks
import Langlands.Geometry.Analytic.CompactQuasiEtaleDiagonal
import Langlands.Geometry.Analytic.ContinuousDomainEmbeddings
import Langlands.Geometry.Analytic.QuasiEtaleCommonProduct

/-! # Compact continuous relative pullbacks over the ambient analytic space -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, v} (K := K)}
  {G : Type z} [Group G] [TopologicalSpace G]

/-- A relative compact pullback inherits the continuous action on its
absolute product as an equivariant analytic domain of that product. -/
def compactContinuousRelativePullback
    {B U V : QuasiEtaleSite X} (f : U ⟶ B) (g : V ⟶ B)
    (σU : G →* Aut U.left) (σV : G →* Aut V.left) (σB : G →* Aut B.left) (σX : G →* Aut X)
    (hB : IsCompactSpace B.left) (hU : IsCompactSpace U.left) (hV : IsCompactSpace V.left)
    (hσU : IsContinuousAction σU) (hσV : IsContinuousAction σV)
    (hf : ∀ a, (σU a).asIso.hom ≫ f.left = f.left ≫ (σB a).asIso.hom)
    (hg : ∀ a, (σV a).asIso.hom ≫ g.left = g.left ≫ (σB a).asIso.hom)
    (hb : ∀ a, (σB a).asIso.hom ≫ B.hom = B.hom ≫ (σX a).asIso.hom) :
    CompactContinuousPullbackData f g σU σV := by
  let c := localizedQuasiEtalePullback U.hom V.hom U.prop
  let d := localizedQuasiEtalePullback B.hom B.hom B.prop
  have hc := IsPullback.of_isLimit c.2
  have hd := IsPullback.of_isLimit d.2
  have hc' : IsPullback c.1.fst c.1.snd (f.left ≫ B.hom) (g.left ≫ B.hom) := by
    simpa only [MorphismProperty.Over.w] using hc
  have hf' : quasiEtale (f.left ≫ B.hom) := (MorphismProperty.Over.w f).symm ▸ U.prop
  let E := compactRelativePullbackOfDiagonal hc' hd hf' B.prop hU hV hB
    (compactQuasiEtaleDiagonalDomain hd hB B.prop)
  let j := domainι c.1.pt E.domain
  let : T2Space (localizedSpaceFunctor.obj U.left) := hU.2
  let : T2Space (localizedSpaceFunctor.obj V.left) := hV.2
  have hUloc := hasLocalDomainEtaleFactorizations_of_quasiEtale (U := U.left) U.prop
  have hVloc := hasLocalDomainEtaleFactorizations_of_quasiEtale (U := V.left) V.prop
  have hQE := ((hUloc.of_isPullback_common hVloc hc).domainι_comp E.domain).quasiEtale
  let W := MorphismProperty.Over.mk ⊤ (j ≫ (c.1.snd ≫ V.hom)) hQE
  let a : W ⟶ U := MorphismProperty.Over.homMk (j ≫ c.1.fst) (by
    change (j ≫ c.1.fst) ≫ U.hom = j ≫ (c.1.snd ≫ V.hom)
    rw [Category.assoc, hc.w])
  let b : W ⟶ V := MorphismProperty.Over.homMk (j ≫ c.1.snd) (Category.assoc _ _ _)
  let t := PullbackCone.mk a b (MorphismProperty.Over.Hom.ext E.isPullback.w)
  have hfx (s : G) : (σU s).asIso.hom ≫ U.hom = U.hom ≫ (σX s).asIso.hom := by
    rw [← MorphismProperty.Over.w f, ← Category.assoc, hf, Category.assoc, hb, ← Category.assoc]
  have hgx (s : G) : (σV s).asIso.hom ≫ V.hom = V.hom ≫ (σX s).asIso.hom := by
    rw [← MorphismProperty.Over.w g, ← Category.assoc, hg, Category.assoc, hb, ← Category.assoc]
  let σ := Langlands.CategoricalPullback.pullbackAction E.isPullback σU σV σB hf hg
  let τ := Langlands.CategoricalPullback.pullbackAction hc σU σV σX hfx hgx
  have hσp := Langlands.CategoricalPullback.pullbackAction_fst E.isPullback σU σV σB hf hg
  have hσq := Langlands.CategoricalPullback.pullbackAction_snd E.isPullback σU σV σB hf hg
  have hτp := Langlands.CategoricalPullback.pullbackAction_fst hc σU σV σX hfx hgx
  have hτq := Langlands.CategoricalPullback.pullbackAction_snd hc σU σV σX hfx hgx
  have hj (s : G) : (σ s).asIso.hom ≫ j = j ≫ (τ s).asIso.hom := by
    apply hc.hom_ext
    · calc
        _ = (σ s).asIso.hom ≫ (j ≫ c.1.fst) := Category.assoc _ _ _
        _ = (j ≫ c.1.fst) ≫ (σU s).asIso.hom := hσp s
        _ = j ≫ ((τ s).asIso.hom ≫ c.1.fst) :=
          (Category.assoc _ _ _).trans (congrArg (j ≫ ·) (hτp s).symm)
        _ = _ := (Category.assoc _ _ _).symm
    · calc
        _ = (σ s).asIso.hom ≫ (j ≫ c.1.snd) := Category.assoc _ _ _
        _ = (j ≫ c.1.snd) ≫ (σV s).asIso.hom := hσq s
        _ = j ≫ ((τ s).asIso.hom ≫ c.1.snd) :=
          (Category.assoc _ _ _).trans (congrArg (j ≫ ·) (hτq s).symm)
        _ = _ := (Category.assoc _ _ _).symm
  have hτ := isContinuousAction_of_isPullback_of_quasiEtale hc U.prop hσU hσV hτp hτq
  have hσ := hτ.of_equivariant_domainEmbedding (isAnalyticDomainEmbedding_domainι c.1.pt E.domain) hj
  exact ⟨t, quasiEtalePullbackIsLimit t E.isPullback, E.compact, σ, hσ, hσp, hσq⟩

end Langlands.Analytic.SaturatedAtlasPresentation
