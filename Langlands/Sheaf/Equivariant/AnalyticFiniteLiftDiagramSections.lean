import Langlands.Sheaf.Equivariant.AnalyticFiniteLiftDiagrams
import Langlands.Sheaf.Equivariant.AnalyticFiniteFixedSections

/-! # Fixed sections on common equivariant analytic lift diagrams -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v z uI uE uA vA wA

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] {ρ : G →* Aut X}
variable {I : Type uI} {E : Type uE}
variable (U : I → QuasiEtaleSite X)
variable (l : ∀ i, ActionLift ρ (U i).hom)
variable (source target : E → I)
variable (arrow : ∀ e, U (source e) ⟶ U (target e))
variable (Q : OpenSubgroup G)
variable {A : Type uA} [Category.{vA} A] {FA : A → A → Type*} {CA : A → Type wA}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{wA} A FA]
variable (F : (TwistedOver quasiEtale ρ)ᵒᵖ ⥤ A)
variable (s : ∀ i, ToType (F.obj (op ((ι quasiEtale ρ).obj (U i)))))

/-- A common equivariant diagram whose subgroup also fixes the supplied
sections for the original analytic lift actions. -/
structure CommonEquivariantFixedLiftDiagram where
  diagram : CommonEquivariantLiftDiagram U l source target arrow Q
  fixes : ∀ i (g : G) (hg : g ∈ diagram.subgroup),
    F.map (liftAction (l i) ⟨g, diagram.le_lift i hg⟩).unop.op (s i) = s i

namespace CommonEquivariantLiftDiagram

variable {U l source target arrow Q}

/-- Shrink a common equivariant diagram until all supplied discrete sections
are fixed, retaining every arrow's equivariance and the prescribed bound. -/
def fixSections [Finite I]
    (d : CommonEquivariantLiftDiagram U l source target arrow Q)
    (hF : (compactLiftSystem ρ).IsDiscrete F)
    (hU : ∀ i, IsCompactSpace (U i).left) :
    CommonEquivariantFixedLiftDiagram U l source target arrow Q F s := by
  let f := finiteLiftFixedSections (fun V => IsCompactSpace V.left)
    F hF U l hU s d.subgroup
  exact {
    diagram := d.shrink f.subgroup f.le_bound
    fixes := fun i g hg => f.fixes i ⟨g, d.le_lift i (f.le_bound hg)⟩ hg
  }

end CommonEquivariantLiftDiagram

/-- Compact-lift compatibility and coefficient discreteness give one common
open subgroup making a finite diagram equivariant and fixing its sections. -/
def commonEquivariantFixedLiftDiagram [Finite I] [Finite E]
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ)
    (hF : (compactLiftSystem ρ).IsDiscrete F)
    (hU : ∀ i, IsCompactSpace (U i).left) :
    CommonEquivariantFixedLiftDiagram U l source target arrow Q F s :=
  (commonEquivariantLiftDiagram U l source target arrow Q hC hU).fixSections F s hF hU

namespace CommonEquivariantFixedLiftDiagram

variable {U l source target arrow Q F s}
variable (d : CommonEquivariantFixedLiftDiagram U l source target arrow Q F s)

/-- Mapping a normalized vertex action back to the original twisted site
recovers the supplied analytic lift action on that subgroup element. -/
theorem subgroupInclusion_map_globalLift_action (i : I)
    (g : (d.diagram.subgroup : Subgroup G)) :
    (subgroupInclusion ρ (d.diagram.subgroup : Subgroup G)).map
        ((d.diagram.globalLift i).action g).unop =
      (liftAction (l i) ⟨(g : G), d.diagram.le_lift i g.property⟩).unop :=
  hom_ext rfl rfl

/-- The supplied section is an actual fixed section for the normalized lift
and the coefficient restricted along the subgroup-inclusion functor. -/
def globalFixedSection (i : I) :
    (d.diagram.globalLift i).FixedSections
      (((subgroupInclusion ρ (d.diagram.subgroup : Subgroup G)).op ⋙ F) ⋙ forget A) := by
  refine ⟨s i, fun g => ?_⟩
  change F.map ((subgroupInclusion ρ (d.diagram.subgroup : Subgroup G)).map
    ((d.diagram.globalLift i).action g).unop).op (s i) = s i
  rw [d.subgroupInclusion_map_globalLift_action]
  exact d.fixes i g g.property

@[simp]
theorem globalFixedSection_val (i : I) :
    (d.globalFixedSection i).val = s i := rfl

end CommonEquivariantFixedLiftDiagram

end Langlands.Sheaf.Equivariant.Analytic
