import Langlands.Geometry.Analytic.FiniteChartFieldPointPullbacks
import Langlands.Geometry.Analytic.InvariantAnalyticDomains
import Langlands.Geometry.Analytic.LocalizedPullbackDescent
import Langlands.Geometry.Analytic.TopChartSpectralTests

/-! # Localized maps from an affinoid spectrum into a chart -/

noncomputable section

universe u v

namespace Langlands.Analytic.SmallAffinoidSpectrum

open CategoryTheory Set PresentedAffinoidAlgebra SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {B : SaturatedAtlasPresentation.{u, v, v} K}
  (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)]

/-- Changing from a chart to a containing chart composes the bounded map
with the actual chart restriction. -/
theorem chartMap_of_subset (j k : B.presentation.atlas.Index)
    (h : range (B.presentation.atlas.chart j) ⊆ range (B.presentation.atlas.chart k))
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra j) R) :
    chartMap R j φ = chartMap R k (φ.comp (B.presentation.atlas.restriction j k h)) := by
  have hi : (𝟙 B : B ⟶ B).baseMap '' range (B.presentation.atlas.chart j) ⊆
      range (B.presentation.atlas.chart k) := by
    change _root_.id '' range (B.presentation.atlas.chart j) ⊆ range (B.presentation.atlas.chart k)
    rwa [image_id]
  calc
    chartMap R j φ = chartMap R j φ ≫ 𝟙 B := (Category.comp_id _).symm
    _ = _ := chartMap_comp R j φ (𝟙 B) k hi

omit [CompleteSpace K] in
private theorem transport_cancel {S R₁ R₂ : PresentedAffinoidAlgebra K}
    (e : R₁ = R₂) (f : BoundedAlgHom K S R₁) :
    (e.symm ▸ (e ▸ f : BoundedAlgHom K S R₂)) = f := by
  cases e
  rfl

/-- Localization retains the complete bounded map into a fixed chart. -/
theorem localizedChartMap_injective (j : B.presentation.atlas.Index) :
    Function.Injective (fun φ : BoundedAlgHom K (B.presentation.atlas.algebra j) R =>
      localizationFunctor.map (chartMap R j φ)) := by
  intro φ ψ h
  have hfg := localizationFunctor_map_injective h
  let i := globalIndex R
  have hcongr (f g : saturated R ⟶ B) (h : f = g)
      (hf : f.baseMap '' range ((saturated R).presentation.atlas.chart i) ⊆
        range (B.presentation.atlas.chart j))
      (hg : g.baseMap '' range ((saturated R).presentation.atlas.chart i) ⊆
        range (B.presentation.atlas.chart j)) : f.pullback i j hf = g.pullback i j hg := by
    subst g
    rfl
  have hpb := hcongr (chartMap R j φ) (chartMap R j ψ) hfg
    (chartMap_admissible R j φ i) (chartMap_admissible R j ψ i)
  have hcast := (chartMap_pullback R j φ _).symm.trans
    (hpb.trans (chartMap_pullback R j ψ _))
  have hback := congrArg (fun q : BoundedAlgHom K (B.presentation.atlas.algebra j)
    ((saturated R).presentation.atlas.algebra i) =>
      (globalAlgebra R ▸ q : BoundedAlgHom K (B.presentation.atlas.algebra j) R)) hcast
  exact (transport_cancel (globalAlgebra R).symm φ).symm.trans
    (hback.trans (transport_cancel (globalAlgebra R).symm ψ))

/-- A localized morphism from a small affinoid spectrum whose image lies
in an actual chart is the map of a unique bounded pullback to that chart. -/
def LocalizedAffinoidChartFactorizationStatement : Prop :=
  ∀ (B : SaturatedAtlasPresentation.{u, v, v} K)
    (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)]
    (j : B.presentation.atlas.Index)
    (f : localizationFunctor.obj (saturated.{u, v} R) ⟶ localizationFunctor.obj B),
    (∀ x, localizedSpaceFunctor.map f x ∈ range (B.presentation.atlas.chart j)) →
    ∃! φ : BoundedAlgHom K (B.presentation.atlas.algebra j) R,
      localizationFunctor.map (chartMap R j φ) = f

theorem localizedAffinoidChartFactorization :
    LocalizedAffinoidChartFactorizationStatement.{u, v} (K := K) := by
  intro B R _ j f hf
  let D := B.chartDomain j
  obtain ⟨l, hl⟩ := exists_localizedDomainLift D f hf
  let t : B.presentation.atlas.SubspaceChart D.carrier := ⟨j, Subset.rfl⟩
  have ht : range ((B.domain D).presentation.atlas.chart t) = univ := by
    change range (B.presentation.atlas.subspaceChart D.carrier t) = univ
    rw [B.presentation.atlas.range_subspaceChart]
    exact eq_univ_of_forall fun x => x.property
  have htop : ∀ k, range ((B.domain D).presentation.atlas.chart k) ⊆
      range ((B.domain D).presentation.atlas.chart t) := fun _ => ht.symm ▸ subset_univ _
  let g := (localizedTopTargetHomEquiv t htop).symm l
  have hg : localizationFunctor.map g = l :=
    (localizedTopTargetHomEquiv_apply t htop g).symm.trans
      ((localizedTopTargetHomEquiv t htop).apply_symm_apply l)
  let F := g ≫ B.domainInclusion D
  have hF : localizationFunctor.map F = f := by
    change localizationFunctor.map (g ≫ B.domainInclusion D) = f
    rw [Functor.map_comp, hg]
    exact hl
  let i := globalIndex R
  have hFj : F.baseMap '' range ((saturated R).presentation.atlas.chart i) ⊆
      range (B.presentation.atlas.chart j) := by
    rintro _ ⟨x, _, rfl⟩
    exact (g.baseMap x).property
  let φ : BoundedAlgHom K (B.presentation.atlas.algebra j) R :=
    globalAlgebra R ▸ F.pullback i j hFj
  have hφ : localizationFunctor.map (chartMap R j φ) = f := by
    change localizationFunctor.map (chartSourceMap i (globalRange R) j
      ((globalAlgebra R).symm ▸ φ)) = f
    rw [transport_cancel, chartSourceMap_eq i (globalRange R) j F hFj]
    exact hF
  exact ⟨φ, hφ, fun ψ hψ => localizedChartMap_injective R j (hψ.trans hφ.symm)⟩

end Langlands.Analytic.SmallAffinoidSpectrum
