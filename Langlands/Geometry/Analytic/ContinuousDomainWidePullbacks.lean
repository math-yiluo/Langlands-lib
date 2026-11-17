import Langlands.Geometry.Analytic.QuasiEtaleDomainWidePullbacks
import Langlands.Geometry.Analytic.ContinuousInvariantDomain

/-! # Continuous action lifts on finite domain-chart wide pullbacks -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, v} (K := K)}
  {G : Type z} [Group G] [TopologicalSpace G] {ρ : G →* Aut X}

namespace ActionLift

variable {U : LocalizedCategory.{u, v, v} (K := K)} {f : U ⟶ X}

/-- The bundled action associated to an actual action lift. -/
abbrev toAction (l : ActionLift ρ f) :
    Action (LocalizedCategory.{u, v, v} (K := K)) l.subgroup where
  V := U
  ρ := (Aut.toEnd U).comp l.action

@[simp]
theorem toAction_ρ (l : ActionLift ρ f) (g : l.subgroup) :
    l.toAction.ρ g = (l.action g).hom := rfl

@[simp]
theorem toAction_ρAut (l : ActionLift ρ f) : l.toAction.ρAut = l.action := by
  ext g
  rfl

/-- Restrict an action lift to an invariant analytic domain, preserving its
open subgroup and deriving continuity from the original Berkovich action. -/
def invariantDomain (l : ActionLift ρ f)
    (D : (presentationOf U).AnalyticDomain)
    (hD : IsInvariantDomain l.toAction D) :
    ActionLift ρ (domainι U D ≫ f) where
  subgroup := l.subgroup
  isOpen_subgroup := l.isOpen_subgroup
  action := (invariantDomainAction l.toAction D hD).ρAut
  isContinuousAction := by
    apply IsContinuousAction.invariantDomainAction
    simpa using l.isContinuousAction
  equivariant g := by
    change domainRestrict D D ((l.action g).hom) (hD g) ≫ (domainι U D ≫ f) =
      (domainι U D ≫ f) ≫ (ρ g).hom
    rw [← Category.assoc, domainRestrict_comp D D ((l.action g).hom) (hD g), Category.assoc,
      l.equivariant, ← Category.assoc]

@[reassoc (attr := simp)]
theorem invariantDomain_inclusion_equivariant (l : ActionLift ρ f)
    (D : (presentationOf U).AnalyticDomain)
    (hD : IsInvariantDomain l.toAction D) (g : l.subgroup) :
    ((l.invariantDomain D hD).action g).hom ≫ domainι U D =
      domainι U D ≫ (l.action g).hom :=
  domainRestrict_comp D D ((l.action g).hom) (hD g)

end ActionLift

namespace FiniteCompactDomainChartCover

variable {U : QuasiEtaleSite X} (C : FiniteCompactDomainChartCover U)
  (l : ActionLift ρ U.hom)
  (σ : ∀ i, l.subgroup →* Aut (C.obj i).left)
  (hσ : ∀ i (g : l.subgroup),
    (σ i g).hom ≫ (C.arrow i).left =
      (C.arrow i).left ≫ (l.action g).hom)

include σ hσ

/-- Equivariance of an actual chart arrow makes its ambient domain invariant.
This uses the stored domain isomorphism, not a pointwise injectivity claim. -/
theorem domain_invariant (i : C.Index) :
    IsInvariantDomain l.toAction (C.domain i) := by
  intro g x hx
  let y : localizedSpaceFunctor.obj (domainObj U.left (C.domain i)) := ⟨x, hx⟩
  let z := localizedSpaceFunctor.map (C.domainIso i).inv y
  have hz : localizedSpaceFunctor.map (C.arrow i).left z = x := by
    change localizedSpaceFunctor.map (C.arrow i).left
      (localizedSpaceFunctor.map (C.domainIso i).inv y) = x
    rw [← TopCat.comp_app, ← Functor.map_comp, C.domainIso_inv_arrow,
      domainι_apply]
  have heq := congrArg (fun k => localizedSpaceFunctor.map k z) (hσ i g)
  simp only [Functor.map_comp, TopCat.comp_app] at heq
  change localizedSpaceFunctor.map (l.action g).hom x ∈ (C.domain i).carrier
  rw [← hz, ← heq]
  exact C.arrow_image_mem i _

variable {J : Type w} [Fintype J] (a : J → C.Index) (j₀ : J)

/-- Every finite nonempty chart intersection is invariant under the same
open subgroup as the compatible chart actions. -/
theorem wideDomain_invariant :
    IsInvariantDomain l.toAction (C.wideDomain a j₀) := by
  intro g x hx
  apply (C.mem_wideDomain a j₀ _).2
  intro j
  exact C.domain_invariant l σ hσ (a j) g x ((C.mem_wideDomain a j₀ x).1 hx j)

/-- The actual wide pullback carries the continuous action induced on its
invariant intersection domain. No new open subgroup is chosen. -/
def wideActionLift : ActionLift ρ (C.wideObj a j₀).hom :=
  l.invariantDomain (C.wideDomain a j₀) (C.wideDomain_invariant l σ hσ a j₀)

@[reassoc (attr := simp)]
theorem wideActionLift_base_equivariant (g : l.subgroup) :
    ((C.wideActionLift l σ hσ a j₀).action g).hom ≫ (C.wideBase a j₀).left =
      (C.wideBase a j₀).left ≫ (l.action g).hom :=
  l.invariantDomain_inclusion_equivariant _ _ g

/-- Every actual wide-pullback projection commutes with the supplied chart
action. The complete morphism equation follows by cancelling the chart arrow. -/
theorem wideActionLift_projection_equivariant (j : J) (g : l.subgroup) :
    ((C.wideActionLift l σ hσ a j₀).action g).hom ≫
        (C.wideProjection a j₀ j).left =
      (C.wideProjection a j₀ j).left ≫ (σ (a j) g).hom := by
  let : Mono (C.arrow (a j)).left := C.arrow_left_mono (a j)
  have hπ : (C.wideProjection a j₀ j).left ≫ (C.arrow (a j)).left =
      (C.wideBase a j₀).left :=
    congrArg (fun k => k.left) (C.wideProjection_comp_arrow a j₀ j)
  apply (cancel_mono (C.arrow (a j)).left).1
  rw [Category.assoc, hπ, Category.assoc, hσ, ← Category.assoc, hπ]
  exact C.wideActionLift_base_equivariant l σ hσ a j₀ g

end FiniteCompactDomainChartCover

end Langlands.Analytic.SaturatedAtlasPresentation
