import Langlands.Geometry.Analytic.ContinuousInvariantDomain
import Langlands.Geometry.Analytic.DomainEtaleFactorizations
import Langlands.Geometry.Analytic.LocalizedQuasiEtalePullbackAction

/-! # Continuity detected by an equivariant analytic-domain embedding -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G]
  {X Y : LocalizedCategory.{u, v, v} (K := K)}

/-- Bundle an action specified by its analytic automorphisms. -/
def analyticActionOfAut (σ : G →* Aut Y) : Action (LocalizedCategory.{u, v, v} (K := K)) G where
  V := Y
  ρ := (Aut.toEnd (X := Y)).comp σ

@[simp]
theorem analyticActionOfAut_ρAut (σ : G →* Aut Y) :
    (analyticActionOfAut σ).ρAut = σ := by
  ext t
  rfl

variable [TopologicalSpace G]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The source of an equivariant analytic-domain embedding into a space
with a continuous action also has a continuous action. -/
theorem IsContinuousAction.of_equivariant_domainEmbedding
    {σX : G →* Aut X} {σY : G →* Aut Y} (hY : IsContinuousAction σY)
    {f : X ⟶ Y} (hf : IsAnalyticDomainEmbedding f)
    (heq : ∀ t, (σX t).asIso.hom ≫ f = f ≫ (σY t).asIso.hom) : IsContinuousAction σX := by
  obtain ⟨D, e, rfl⟩ := hf
  let Y' := analyticActionOfAut σY
  let j := domainι Y D
  have hD : IsInvariantDomain Y' D := by
    intro t y hy
    let z : localizedSpaceFunctor.obj (domainObj Y D) := ⟨y, hy⟩
    let x := localizedSpaceFunctor.map e.inv z
    have hx : localizedSpaceFunctor.map (e.hom ≫ j) x = y := by
      change localizedSpaceFunctor.map (e.hom ≫ j) (localizedSpaceFunctor.map e.inv z) = y
      rw [← TopCat.comp_app, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_assoc]
      exact domainι_apply D z
    have hpoint := congrArg (fun f : X ⟶ Y => localizedSpaceFunctor.map f x) (heq t)
    simp only [CategoryTheory.Functor.map_comp, TopCat.comp_app] at hpoint
    change localizedSpaceFunctor.map (σY t).asIso.hom y ∈ D.carrier
    rw [← hx, CategoryTheory.Functor.map_comp, TopCat.comp_app, ← hpoint]
    change localizedSpaceFunctor.map (domainι Y D) _ ∈ D.carrier
    rw [domainι_apply]
    exact (Subtype.property _)
  have hY' : IsContinuousAction Y'.ρAut := by
    simpa only [Y', analyticActionOfAut_ρAut] using hY
  let Z := SaturatedAtlasPresentation.invariantDomainAction Y' D hD
  have hZ : IsContinuousAction Z.ρAut := hY'.invariantDomainAction D hD
  have hZι (t : G) : (Z.ρAut t).asIso.hom ≫ j = j ≫ (σY t).asIso.hom :=
    (invariantDomainInclusion Y' D hD).comm t
  have hXe (t : G) : (σX t).asIso.hom ≫ e.hom = e.hom ≫ (Z.ρAut t).asIso.hom := by
    apply (cancel_mono j).1
    calc
      _ = (σX t).asIso.hom ≫ (e.hom ≫ j) := Category.assoc _ _ _
      _ = (e.hom ≫ j) ≫ (σY t).asIso.hom := heq t
      _ = _ := by rw [Category.assoc, Category.assoc, hZι]
  apply hZ.of_equivariant_iso e.symm σX
  intro t
  change (Z.ρAut t).asIso.hom ≫ e.inv = e.inv ≫ (σX t).asIso.hom
  apply (cancel_mono e.hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, hXe,
    Iso.inv_hom_id_assoc]

end Langlands.Analytic.SaturatedAtlasPresentation
