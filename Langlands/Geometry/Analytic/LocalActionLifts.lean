import Langlands.Geometry.Analytic.QuasiEtaleSite
import Langlands.Geometry.Analytic.ContinuousAnalyticAction

/-! # Lifts of group actions to compact quasi-étale and distinguished étale objects -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- An analytic space is compact if its underlying space is compact and Hausdorff. -/
def IsCompactSpace (U : LocalizedCategory.{u, v, v} (K := K)) : Prop :=
  CompactSpace (localizedSpaceFunctor.obj U) ∧ T2Space (localizedSpaceFunctor.obj U)

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] [TopologicalSpace G]

/-- A lift of the action `ρ` of `G` on `X` to a morphism `f : U ⟶ X`: an open subgroup `H` of
`G`, a continuous action of `H` on `U`, and equivariance of `f`, i.e. the action of each
`h ∈ H` on `U` covers the action of `h` on `X`. -/
structure ActionLift (ρ : G →* Aut X) {U : LocalizedCategory.{u, v, v} (K := K)}
    (f : U ⟶ X) where
  /-- The open subgroup `H`. -/
  subgroup : Subgroup G
  isOpen_subgroup : IsOpen (subgroup : Set G)
  /-- The action of `H` on `U`. -/
  action : subgroup →* Aut U
  isContinuousAction : IsContinuousAction action
  /-- `f` is `H`-equivariant. -/
  equivariant : ∀ h : subgroup, (action h).hom ≫ f = f ≫ (ρ h).hom

namespace ActionLift

variable {ρ : G →* Aut X} {U : LocalizedCategory.{u, v, v} (K := K)} {f : U ⟶ X}

/-- Two lifts agree on an open subgroup `N` contained in both of their subgroups. -/
def AgreeOn (a b : ActionLift ρ f) (N : Subgroup G) : Prop :=
  IsOpen (N : Set G) ∧ ∃ (ha : N ≤ a.subgroup) (hb : N ≤ b.subgroup),
    ∀ (g : G) (hg : g ∈ N), a.action ⟨g, ha hg⟩ = b.action ⟨g, hb hg⟩

/-- Restriction of a lift to a smaller open subgroup. -/
def restrict (a : ActionLift ρ f) (N : Subgroup G)
    (hN : IsOpen (N : Set G)) (hle : N ≤ a.subgroup) : ActionLift ρ f where
  subgroup := N
  isOpen_subgroup := hN
  action := a.action.comp (Subgroup.inclusion hle)
  isContinuousAction := a.isContinuousAction.comp
    ⟨Subgroup.inclusion hle, continuous_inclusion hle⟩
  equivariant h := a.equivariant (Subgroup.inclusion hle h)

@[simp]
theorem restrict_action_apply (a : ActionLift ρ f) (N : Subgroup G)
    (hN : IsOpen (N : Set G)) (hle : N ≤ a.subgroup) (h : N) :
    (a.restrict N hN hle).action h = a.action (Subgroup.inclusion hle h) := rfl

end ActionLift

/-- Berkovich's distinguished étale morphisms: `U → X` factors as `U ⥲ O ⊂ Ū → X` with `Ū`
compact, `Ū → X` quasi-étale, and `O` an open analytic domain of `Ū` whose complement is an
analytic domain (a distinguished open subset). -/
def IsDistinguishedEtale {U : LocalizedCategory.{u, v, v} (K := K)} (f : U ⟶ X) : Prop :=
  etale f ∧ ∃ (Ubar : LocalizedCategory.{u, v, v} (K := K)) (φ : Ubar ⟶ X),
    quasiEtale φ ∧ IsCompactSpace Ubar ∧
    ∃ (O D : (localizedObjectEquiv.symm Ubar).AnalyticDomain),
      IsOpen O.carrier ∧ D.carrier = O.carrierᶜ ∧
      ∃ e : U ≅ localizationFunctor.obj ((localizedObjectEquiv.symm Ubar).domain O),
        f = e.hom ≫ (localizedObjectEquiv.symm Ubar).localizedDomainInclusion O ≫ φ

end Langlands.Analytic.SaturatedAtlasPresentation
