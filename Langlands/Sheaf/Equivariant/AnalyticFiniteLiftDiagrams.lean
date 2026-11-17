import Langlands.Sheaf.Equivariant.AnalyticFreeRepresentable

/-! # Common subgroup actions for finite diagrams of compact analytic lifts -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v z uI uE

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] {ρ : G →* Aut X}
variable {I : Type uI} {E : Type uE}
variable (U : I → QuasiEtaleSite X)
variable (l : ∀ i, ActionLift ρ (U i).hom)
variable (source target : E → I)
variable (arrow : ∀ e, U (source e) ⟶ U (target e))
variable (Q : OpenSubgroup G)

/-- One open subgroup on which a supplied family of ordinary arrows
intertwines all chosen analytic lifts, below a prescribed bound. -/
structure CommonEquivariantLiftDiagram where
  subgroup : OpenSubgroup G
  le_bound : subgroup ≤ Q
  le_lift : ∀ i, (subgroup : Subgroup G) ≤ (l i).subgroup
  equivariant : ∀ e (g : G) (hg : g ∈ subgroup),
    ((l (source e)).action ⟨g, le_lift (source e) hg⟩).hom ≫ (arrow e).left =
      (arrow e).left ≫ ((l (target e)).action ⟨g, le_lift (target e) hg⟩).hom

/-- Pairwise compatibility makes finitely many supplied arrows equivariant
on a common open subgroup, with every vertex action defined there. -/
theorem nonempty_commonEquivariantLiftDiagram [Finite I] [Finite E]
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ)
    (hU : ∀ i, IsCompactSpace (U i).left) :
    Nonempty (CommonEquivariantLiftDiagram U l source target arrow Q) := by
  classical
  choose N hN hNt hNs hf using fun e =>
    hC (arrow e) (hU (target e)) (hU (source e)) (l (target e)) (l (source e))
  let A : E → OpenSubgroup G := fun e => ⟨N e, hN e⟩
  let M : OpenSubgroup G :=
    Q ⊓ (OpenSubgroup.iInfOfFinite (fun i => liftOpenSubgroup (l i)) ⊓
      OpenSubgroup.iInfOfFinite A)
  have hMl (i : I) : M ≤ liftOpenSubgroup (l i) :=
    inf_le_right.trans (inf_le_left.trans
      (OpenSubgroup.iInfOfFinite_le (fun i => liftOpenSubgroup (l i)) i))
  have hMA (e : E) : M ≤ A e :=
    inf_le_right.trans (inf_le_right.trans (OpenSubgroup.iInfOfFinite_le A e))
  exact ⟨{
    subgroup := M
    le_bound := inf_le_left
    le_lift := hMl
    equivariant := fun e g hg => hf e g (hMA e hg)
  }⟩

/-- Choose common subgroup data for a finite family of compact lifted
objects and ordinary arrows, under explicit lift compatibility. -/
def commonEquivariantLiftDiagram [Finite I] [Finite E]
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ)
    (hU : ∀ i, IsCompactSpace (U i).left) :
    CommonEquivariantLiftDiagram U l source target arrow Q :=
  Classical.choice
    (nonempty_commonEquivariantLiftDiagram U l source target arrow Q hC hU)

namespace CommonEquivariantLiftDiagram

variable {U l source target arrow Q}
variable (d : CommonEquivariantLiftDiagram U l source target arrow Q)

/-- Common equivariance persists after a further open subgroup restriction. -/
def shrink (H : OpenSubgroup G) (hH : H ≤ d.subgroup) :
    CommonEquivariantLiftDiagram U l source target arrow Q where
  subgroup := H
  le_bound := hH.trans d.le_bound
  le_lift i := fun _ hg => d.le_lift i (hH hg)
  equivariant e g hg := d.equivariant e g (hH hg)

/-- The chosen analytic lift restricted to the common subgroup retains its
actual continuous analytic action and its map to the original base. -/
def restrictedLift (i : I) : ActionLift ρ (U i).hom :=
  (l i).restrict d.subgroup d.subgroup.isOpen (d.le_lift i)

/-- Normalize the restricted action to a global lift for the common
subgroup acting on the original quasi-etale site. -/
def globalLift (i : I) :
    GlobalLift (P := quasiEtale) (ρ := ρ.comp (d.subgroup : Subgroup G).subtype) :=
  liftGlobalLift (U i) (l i) d.subgroup (d.le_lift i)

/-- Every supplied ordinary arrow is equivariant for the normalized
global lifts, with the inverse twist convention of the twisted site. -/
theorem globalLift_equivariant (e : E) (g : (d.subgroup : Subgroup G)) :
    ((d.globalLift (source e)).action g).unop ≫
        (ι quasiEtale (ρ.comp (d.subgroup : Subgroup G).subtype)).map (arrow e) =
      (ι quasiEtale (ρ.comp (d.subgroup : Subgroup G).subtype)).map (arrow e) ≫
        ((d.globalLift (target e)).action g).unop := by
  refine hom_ext ((one_mul _).trans (mul_one _).symm) ?_
  exact d.equivariant e ((g⁻¹ : (d.subgroup : Subgroup G)) : G) (g⁻¹).property

/-- Each normalized compact vertex lift is eventually equivariant for all
admissible local actions of the common subgroup, under explicit compatibility. -/
theorem globalLift_eventuallyEquivariant
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ)
    (hU : ∀ i, IsCompactSpace (U i).left) (i : I) :
    (d.globalLift i).EventuallyEquivariant
      (compactLiftSystem (ρ.comp (d.subgroup : Subgroup G).subtype)) :=
  liftGlobalLift_eventuallyEquivariant (U i) (l i) d.subgroup (d.le_lift i) hC (hU i)

end CommonEquivariantLiftDiagram

end Langlands.Sheaf.Equivariant.Analytic
