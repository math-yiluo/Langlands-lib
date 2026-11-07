import Langlands.GroupScheme.HomScheme.TorusSubgroupChartStatements
import Langlands.GroupScheme.HomScheme.AdmissibleChartGluing
import Langlands.GroupScheme.HomScheme.AdmissibleClosedRepresentability
import Langlands.AlgebraicGeometry.ClosedSubschemeGluing

/-! # Gluing open charts into the smooth moduli of closed torus subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S} (F : SubgroupFunctor G)

/-- A Zariski-local subgroup which is admissible after base change to every
member of an open cover of the base has a closed scheme representative of its
absolute membership condition. -/
theorem exists_isSchemeRepresentedBy (hF : IsZariskiLocal F)
    (𝒰 : Scheme.OpenCover.{u} S)
    (h : ∀ i, TorusSubgroupModuli.IsAdmissible (F.baseChange (𝒰.f i))) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ G.X.left), IsClosedImmersion j ∧
      F.IsSchemeRepresentedBy j := by
  choose L c hc hL using F.exists_localClosedSubscheme 𝒰 h
  let 𝒱 : G.X.left.OpenCover := 𝒰.pullback₁ G.X.hom
  obtain ⟨L₀, c₀, hc₀, hfac⟩ :=
    Scheme.ClosedSubschemeGluing.exists_isClosedImmersion
      (P := fun _ x => F.schemeCondition x)
      (fun _ _ a z hz => F.schemeCondition_comp z a hz)
      (fun i : 𝒰.I₀ => 𝒱.f i) c (fun i _ z => hL i _ z)
      (fun x => ⟨𝒱.idx x, 𝒱.covers x⟩)
      (fun Z z hz => by
        choose U hU hPU using hz
        let 𝒲 : Z.OpenCover := Scheme.Cover.mkOfCovers Z (fun p => (U p : Scheme.{u}))
          (fun p => (U p).ι) (fun p => ⟨p, ⟨p, hU p⟩, rfl⟩)
        exact (F.schemeCondition_iff_openCover hF z 𝒲).mpr hPU)
  exact ⟨L₀, c₀, hc₀, fun _ x => hfac x⟩

end Langlands.GroupScheme.SubgroupFunctor

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}}

/-- Matching local admissible families always descend to an admissible
subgroup. -/
theorem hasEffectiveAdmissibleDescent (G : GroupScheme S) :
    HasEffectiveAdmissibleDescent G := by
  intro T 𝒰 F hF
  have hb : ∀ i, IsAdmissible ((matchingSubgroup 𝒰 F).baseChange (𝒰.f i)) := fun i => by
    rw [baseChange_matchingSubgroup 𝒰 F hF i]
    exact (coverSubgroup 𝒰 F i).property
  obtain ⟨Z, c, hc, h⟩ := (matchingSubgroup 𝒰 F).exists_isSchemeRepresentedBy
    (isZariskiLocal_matchingSubgroup 𝒰 F) 𝒰 hb
  exact isAdmissible_matchingSubgroup_of_isClosedRepresentable 𝒰 F hF
    ((matchingSubgroup 𝒰 F).isClosedRepresentable_of_schemeCondition c h)

/-- **Chart gluing.** A chart cover of every smooth affine group scheme yields
the smooth moduli scheme of its closed torus subgroups. -/
theorem chartGluing : ChartGluingStatement.{u} := by
  intro hcov S G _ _
  obtain ⟨ι, U, K, j, hj, hc⟩ := hcov S G
  exact OpenCharts.exists_smooth_universal j hj (hasEffectiveAdmissibleDescent G) hc

end Langlands.GroupScheme.TorusSubgroupModuli
