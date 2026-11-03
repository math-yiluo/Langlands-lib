import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionQuotientCoverSystem
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationEtaleObjectDescent

/-! # Stable systems for quotients of affine étale actions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.AffineFiniteTypeFirstLevel

variable {H : EtaleEquivalenceRelation.{u}} [IsAffine H.U]
  (M : AffineFiniteTypeFirstLevel H)
  {P : Scheme.{u}} [IsAffine P] (p : P ⟶ H.U) [Etale p] (A : Action H p)
  (C : A.relation.InvariantAffineQuotientCover)
  (C₂ : A.pairAction.relation.InvariantAffineQuotientCover)
  (Qc : A.relation.SchemeQuotient) (Q₂c : A.pairAction.relation.SchemeQuotient)
  {E : EtaleEquivalenceRelation.{u}}
  (φ : E ⟶ A.quotientRelation Qc Q₂c) [IsIso φ.objMap]

/-- A first level of the acting relation and finite invariant affine quotient
covers for an affine étale action and its pair action give a finite type
cartesian system for their quotient relation. -/
def actionQuotientSystem : FiniteTypeCartesianSystem E := by
  let h := M.comparison.isCartesian
  letI : IsNoetherianRing Γ(M.relation.U, ⊤) := inferInstance
  letI := h.stableIndex_isCofiltered
  let S := h.stableEtaleActionModel p A
  letI := S.affine
  letI := S.etale
  let D := Over.forget S.index ⋙ h.stableDiagram
  let c := h.stableCone.whisker (Over.forget S.index)
  let t := ActionDiagram.overComparison h.stableDiagram S.index
  let B := ActionDiagram.ofComparison t S.action
  let T := ActionDiagram.ActionCone.ofComparison t S.action (c := c) (p := p)
    (k := S.comparison)
    (h.stableCone.π.app S.index)
    (ActionDiagram.whisker_overComparison h.stableDiagram h.stableCone S.index)
    S.square A S.equivariant
  letI : ∀ i : Over S.index, IsAffine (D.obj i).U := fun i =>
    inferInstanceAs (IsAffine (h.stableDiagram.obj i.left).U)
  letI : ∀ i : Over S.index, IsAffine (D.obj i).R := fun i =>
    inferInstanceAs (IsAffine (h.stableDiagram.obj i.left).R)
  letI : ∀ i : Over S.index, IsAffine (B.points.obj i) := by
    intro i
    change IsAffine (pullback (h.stableDiagram.map i.hom).objMap S.projection)
    infer_instance
  letI : ∀ i : Over S.index, LocallyOfFiniteType (terminal.from (B.points.obj i)) := by
    intro i
    let : LocallyOfFiniteType (terminal.from (D.obj i).U) :=
      h.stableDiagram_locallyOfFiniteType i.left
    rw [show terminal.from (B.points.obj i) =
      B.proj i ≫ terminal.from (D.obj i).U from terminal.hom_ext _ _]
    infer_instance
  exact B.finiteTypeCartesianSystemOfCovers T C C₂ Qc Q₂c
    (CartesianDiagram.isLimitObjectAbove h.stableDiagram S.index h.stableCone
      h.stableCone_isLimitObject) φ

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.AffineFiniteTypeFirstLevel
