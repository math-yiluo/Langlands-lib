import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactTupleCones
import Langlands.Geometry.Analytic.CompactRelativePullbackConstruction
import Langlands.CategoryTheory.FiniteWidePullbackCones

/-! # Compact compatible tuple cones from compact continuous relative pullbacks -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, v} (K := K)}
  {G : Type z} [Group G] [TopologicalSpace G] {ρ : G →* Aut X}

namespace CompactCompatibleCover

variable {i : CompactLiftBasis ρ} (c : CompactCompatibleCover ρ i)

/-- Restrict the target action to the cover's specified common subgroup. -/
abbrev targetAction : c.subgroup →* Aut (compactLiftBasisObject ρ i).left :=
  c.targetLift.action.comp (Subgroup.inclusion c.le_target)

/-- Restrict a chosen source action to the same specified common subgroup. -/
abbrev sourceAction (j : Fin c.cover.size) :
    c.subgroup →* Aut (compactLiftBasisObject ρ (c.cover.index j)).left :=
  (c.sourceLift j).action.comp (Subgroup.inclusion (c.le_source j))

/-- Restriction to the common subgroup preserves Berkovich continuity. -/
theorem sourceAction_continuous (j : Fin c.cover.size) :
    IsContinuousAction (c.sourceAction j) :=
  (c.sourceLift j).isContinuousAction.comp
    ⟨Subgroup.inclusion (c.le_source j), continuous_inclusion (c.le_source j)⟩

/-- The twisted compatibility equation gives ordinary analytic equivariance
for the common-subgroup actions, by applying it at the inverse element. -/
theorem sourceAction_equivariant (j : Fin c.cover.size) (a : c.subgroup) :
    (c.sourceAction j a).asIso.hom ≫ (c.cover.arrow j).left =
      (c.cover.arrow j).left ≫ (c.targetAction a).asIso.hom := by
  have h := congrArg Hom.left
    (c.equivariant j (a : G)⁻¹ (c.subgroup.inv_mem a.property))
  simp only [comp_left, liftAction_left] at h
  have hs : (⟨(a : G)⁻¹, c.le_source j (c.subgroup.inv_mem a.property)⟩ :
      (c.sourceLift j).subgroup)⁻¹ = Subgroup.inclusion (c.le_source j) a := by
    apply Subtype.ext
    exact inv_inv (a : G)
  have ht : (⟨(a : G)⁻¹, c.le_target (c.subgroup.inv_mem a.property)⟩ :
      c.targetLift.subgroup)⁻¹ = Subgroup.inclusion c.le_target a := by
    apply Subtype.ext
    exact inv_inv (a : G)
  rw [hs, ht] at h
  exact h

end CompactCompatibleCover

variable {i : CompactLiftBasis ρ} (c : CompactCompatibleCover ρ i)

/-- A positive tuple cone with its continuous action on the exact common
subgroup and full equivariance of the base and all projections. -/
structure CompactCompatibleTupleConeData (n : ℕ)
    (α : Fin (n + 1) → Fin c.cover.size) where
  cone : WidePullbackCone (fun j => c.cover.arrow (α j))
  isLimit : IsLimit cone
  compact : IsCompactSpace cone.pt.left
  action : c.subgroup →* Aut cone.pt.left
  continuous : IsContinuousAction action
  base_equivariant : ∀ a, (action a).asIso.hom ≫ cone.base.left =
    cone.base.left ≫ (c.targetAction a).asIso.hom
  projection_equivariant : ∀ j a, (action a).asIso.hom ≫ (cone.π j).left =
    (cone.π j).left ≫ (c.sourceAction (α j) a).asIso.hom

/-- The positive induction starts with the supplied first source and its
restricted continuous action. -/
def compactTupleSingleton (α : Fin 1 → Fin c.cover.size) :
    CompactCompatibleTupleConeData c 0 α where
  cone := Langlands.FiniteWidePullback.singletonCone (fun j => c.cover.arrow (α j))
  isLimit := Langlands.FiniteWidePullback.singletonIsLimit (fun j => c.cover.arrow (α j))
  compact := (c.cover.index (α 0)).property.1
  action := c.sourceAction (α 0)
  continuous := c.sourceAction_continuous (α 0)
  base_equivariant := c.sourceAction_equivariant (α 0)
  projection_equivariant := by
    intro j a
    have hj : j = 0 := Fin.eq_zero j
    subst j
    change (c.sourceAction (α 0) a).asIso.hom ≫ 𝟙 _ = 𝟙 _ ≫ (c.sourceAction (α 0) a).asIso.hom
    rw [Category.comp_id, Category.id_comp]

/-- The successor step uses one compact continuous binary pullback. Its
subgroup and full projection equations are retained for further induction. -/
def compactTupleCons
    {n : ℕ} (α : Fin (n + 2) → Fin c.cover.size)
    (s : CompactCompatibleTupleConeData c n (fun j => α j.succ)) :
    CompactCompatibleTupleConeData c (n + 1) α := by
  let ρ' := ρ.comp c.subgroup.toSubgroup.subtype
  let p := compactContinuousRelativePullback (c.cover.arrow (α 0)) s.cone.base
    (c.sourceAction (α 0)) s.action c.targetAction ρ' i.property.1
    (c.cover.index (α 0)).property.1 s.compact
    (c.sourceAction_continuous (α 0)) s.continuous
    (c.sourceAction_equivariant (α 0)) s.base_equivariant
    (fun a => c.targetLift.equivariant (Subgroup.inclusion c.le_target a))
  exact {
    cone := Langlands.FiniteWidePullback.consCone (fun j => c.cover.arrow (α j)) s.cone p.cone
    isLimit := Langlands.FiniteWidePullback.consIsLimit (fun j => c.cover.arrow (α j))
      s.cone p.cone s.isLimit p.isLimit
    compact := p.compact
    action := p.action
    continuous := p.continuous
    base_equivariant := by
      intro a
      change (p.action a).asIso.hom ≫ (p.cone.fst.left ≫ (c.cover.arrow (α 0)).left) =
        (p.cone.fst.left ≫ (c.cover.arrow (α 0)).left) ≫ (c.targetAction a).asIso.hom
      rw [← Category.assoc, p.fst_equivariant, Category.assoc,
        c.sourceAction_equivariant, ← Category.assoc]
    projection_equivariant := by
      intro j a
      refine Fin.cases ?_ (fun k => ?_) j
      · exact p.fst_equivariant a
      · change (p.action a).asIso.hom ≫ (p.cone.snd.left ≫ (s.cone.π k).left) =
          (p.cone.snd.left ≫ (s.cone.π k).left) ≫ (c.sourceAction (α k.succ) a).asIso.hom
        rw [← Category.assoc, p.snd_equivariant, Category.assoc,
          s.projection_equivariant, ← Category.assoc]
  }

/-- Positive tuple induction retains continuous compatible actions in every degree. -/
def compactCompatibleTupleCone :
    (n : ℕ) → (α : Fin (n + 1) → Fin c.cover.size) →
      CompactCompatibleTupleConeData c n α
  | 0, α => compactTupleSingleton c α
  | n + 1, α => compactTupleCons c α
      (compactCompatibleTupleCone n (fun j => α j.succ))

namespace CompactCompatibleTupleConeData

variable {c} {n : ℕ} {α : Fin (n + 1) → Fin c.cover.size}
  (d : CompactCompatibleTupleConeData c n α)

/-- The constructed subgroup action gives an actual action lift over `X`. -/
def actionLift : ActionLift ρ d.cone.pt.hom where
  subgroup := c.subgroup
  isOpen_subgroup := c.subgroup.isOpen'
  action := d.action
  isContinuousAction := d.continuous
  equivariant a := by
    have hw := MorphismProperty.Over.w d.cone.base
    calc
      (d.action a).asIso.hom ≫ d.cone.pt.hom =
          (d.action a).asIso.hom ≫ (d.cone.base.left ≫ (compactLiftBasisObject ρ i).hom) :=
        congrArg (fun k => (d.action a).asIso.hom ≫ k) hw.symm
      _ = ((d.action a).asIso.hom ≫ d.cone.base.left) ≫ (compactLiftBasisObject ρ i).hom :=
        (Category.assoc _ _ _).symm
      _ = (d.cone.base.left ≫ (c.targetAction a).asIso.hom) ≫ (compactLiftBasisObject ρ i).hom :=
        congrArg (fun k => k ≫ (compactLiftBasisObject ρ i).hom) (d.base_equivariant a)
      _ = d.cone.base.left ≫ ((c.targetAction a).asIso.hom ≫ (compactLiftBasisObject ρ i).hom) :=
        Category.assoc _ _ _
      _ = d.cone.base.left ≫ ((compactLiftBasisObject ρ i).hom ≫ (ρ (a : G)).asIso.hom) :=
        congrArg (fun k => d.cone.base.left ≫ k)
          (c.targetLift.equivariant (Subgroup.inclusion c.le_target a))
      _ = (d.cone.base.left ≫ (compactLiftBasisObject ρ i).hom) ≫ (ρ (a : G)).asIso.hom :=
        (Category.assoc _ _ _).symm
      _ = d.cone.pt.hom ≫ (ρ (a : G)).asIso.hom :=
        congrArg (fun k => k ≫ (ρ (a : G)).asIso.hom) hw

/-- Every constructed point lies in the original compact lift basis. -/
def basisPoint : CompactLiftBasis ρ :=
  ⟨d.cone.pt, d.compact, ⟨d.actionLift⟩⟩

end CompactCompatibleTupleConeData

/-- Every positive tuple of a compatible compact cover has a limiting cone
with compact vertex and a continuous lift of the ambient action. -/
theorem compactCompatibleTupleCones : CompactCompatibleTupleConesStatement ρ := by
  intro i c n α
  let d := compactCompatibleTupleCone c n α
  exact ⟨d.cone, ⟨d.isLimit⟩, d.compact, ⟨d.actionLift⟩⟩

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
