import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionQuotientCovers

/-! # Finite type quotient systems from two finite invariant covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.ActionDiagram

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ EtaleEquivalenceRelation.{u}} (A : ActionDiagram D)
  {c : Cone D} (T : A.ActionCone c)
  [∀ i, IsAffine (D.obj i).U] [∀ i, IsAffine (D.obj i).R]
  [∀ i, IsAffine (A.points.obj i)]
  [∀ i, LocallyOfFiniteType (terminal.from (A.points.obj i))]
  (C : T.action.relation.InvariantAffineQuotientCover)
  (C₂ : T.action.pairAction.relation.InvariantAffineQuotientCover)
  (Qc : T.action.relation.SchemeQuotient)
  (Q₂c : T.action.pairAction.relation.SchemeQuotient)
  (hc : IsLimit (objectFunctor.mapCone c))
  {E : EtaleEquivalenceRelation.{u}}
  (φ : E ⟶ T.action.quotientRelation Qc Q₂c) [IsIso φ.objMap]

/-- Two finite invariant affine quotient covers over the limit yield a
finite type cartesian system for the supplied quotient relation. -/
def finiteTypeCartesianSystemOfCovers : FiniteTypeCartesianSystem E := by
  letI : ∀ i, IsAffine (A.relationDiagram.obj i).U := fun i =>
    inferInstanceAs (IsAffine (A.points.obj i))
  letI : ∀ i, IsAffine (A.relationDiagram.obj i).R := fun i =>
    (A.action i).isAffine_relation
  letI : ∀ i, IsAffine (A.pair.points.obj i) := by
    intro i
    change IsAffine (pullback (A.proj i) (A.proj i))
    infer_instance
  letI : ∀ i, IsAffine (A.pair.relationDiagram.obj i).U := fun i =>
    inferInstanceAs (IsAffine (A.pair.points.obj i))
  letI : ∀ i, IsAffine (A.pair.relationDiagram.obj i).R := fun i =>
    (A.pair.action i).isAffine_relation
  letI := C.finite
  letI := C₂.finite
  let M := InvariantAffineQuotientCover.descend A.relationDiagram (A.relationCone T)
    (A.isLimitRelationConeObject T hc) C
  let M₂ := InvariantAffineQuotientCover.descend A.pair.relationDiagram
    (A.pair.relationCone T.pair) (A.pair.isLimitRelationConeObject T.pair hc) C₂
  let j := IsCofiltered.min M.index M₂.index
  let A' := A.whisker (Over.forget j)
  let T' := ActionCone.whisker A T (Over.forget j)
  let Q : ∀ X : Over j, (A'.action X).relation.SchemeQuotient := fun X =>
    (M.coverAt (X.hom ≫ IsCofiltered.minToLeft M.index M₂.index)).schemeQuotient
  let Q₂ : ∀ X : Over j, (A'.action X).pairAction.relation.SchemeQuotient := fun X =>
    (M₂.coverAt (X.hom ≫ IsCofiltered.minToRight M.index M₂.index)).schemeQuotient
  letI : ∀ X : Over j, IsAffine (A'.points.obj X) := fun X =>
    inferInstanceAs (IsAffine (A.points.obj X.left))
  letI : ∀ X : Over j, LocallyOfFiniteType (terminal.from (A'.points.obj X)) := fun X =>
    inferInstanceAs (LocallyOfFiniteType (terminal.from (A.points.obj X.left)))
  letI : ∀ X : Over j, IsAffineHom (A'.proj X) := by
    intro X
    change IsAffineHom (A.proj X.left)
    infer_instance
  letI : ∀ X : Over j, QuasiSeparatedSpace (pullback (A'.proj X) (A'.proj X) : Scheme.{u}) := by
    intro X
    change QuasiSeparatedSpace (pullback (A.proj X.left) (A.proj X.left) : Scheme.{u})
    infer_instance
  letI : ∀ X : Over j, IsAffineHom (Q X).q := fun X =>
    inferInstanceAs (IsAffineHom
      (M.coverAt (X.hom ≫ IsCofiltered.minToLeft M.index M₂.index)).schemeQuotient.q)
  exact A'.finiteTypeCartesianSystem T' Q Q₂ Qc Q₂c
    (CartesianDiagram.isLimitObjectAbove D j c hc) φ (fun {X Y} a => by
      change IsAffineHom (D.map a.left).objMap
      infer_instance)

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.ActionDiagram
