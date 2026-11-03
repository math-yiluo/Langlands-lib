import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionQuotientDiagram
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationQuotientOpenCover

/-! # Diagonal pairs and restriction of quotient covers in action diagrams -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

namespace ActionDiagram

variable {I : Type u} [Category.{u} I] {D : I ⥤ EtaleEquivalenceRelation.{u}}
  (A : ActionDiagram D)

/-- The diagram of diagonal pair actions. -/
def pair : ActionDiagram D where
  points :=
    { obj i := pullback (A.proj i) (A.proj i)
      map a := Action.pairObjMap (A.proj_w a)
      map_id i := by apply pullback.hom_ext <;> simp
      map_comp a b := by apply pullback.hom_ext <;> simp }
  proj i := pullback.fst (A.proj i) (A.proj i) ≫ A.proj i
  proj_w a := Action.pairObjMap_w (A.proj_w a)
  action i := (A.action i).pairAction
  etale i := by infer_instance
  isEquivariant a := Action.isEquivariant_pairObjMap (A.isEquivariant a)
  isPullback a := (Action.isPullback_pairObjMap (A.proj_w a) (A.isPullback a)).paste_vert
    (A.isPullback a)

variable {c : Cone D} (T : A.ActionCone c)

/-- The diagonal pair action over the cone point. -/
def ActionCone.pair : A.pair.ActionCone c where
  P := pullback T.proj T.proj
  proj := pullback.fst T.proj T.proj ≫ T.proj
  action := T.action.pairAction
  etale := by infer_instance
  leg i := Action.pairObjMap (T.leg_w i)
  leg_w i := Action.pairObjMap_w (T.leg_w i)
  leg_comp a := by
    change Action.pairObjMap (T.leg_w _) ≫ Action.pairObjMap (A.proj_w a) =
      Action.pairObjMap (T.leg_w _)
    apply pullback.hom_ext <;> simp [T.leg_comp a]
  isEquivariant i := Action.isEquivariant_pairObjMap (T.isEquivariant i)
  isPullback i := (Action.isPullback_pairObjMap (T.leg_w i) (T.isPullback i)).paste_vert
    (T.isPullback i)

variable {J : Type u} [Category.{u} J] (F : J ⥤ I)

/-- Restrict a diagram of actions along a functor. -/
def whisker : ActionDiagram (F ⋙ D) where
  points := F ⋙ A.points
  proj j := A.proj (F.obj j)
  proj_w a := A.proj_w (F.map a)
  action j := A.action (F.obj j)
  etale j := A.etale (F.obj j)
  isEquivariant a := A.isEquivariant (F.map a)
  isPullback a := A.isPullback (F.map a)

/-- Restrict the compatible action over a cone point. -/
def ActionCone.whisker : (A.whisker F).ActionCone (c.whisker F) where
  P := T.P
  proj := T.proj
  action := T.action
  etale := T.etale
  leg j := T.leg (F.obj j)
  leg_w j := T.leg_w (F.obj j)
  leg_comp a := T.leg_comp (F.map a)
  isEquivariant j := T.isEquivariant (F.obj j)
  isPullback j := T.isPullback (F.obj j)

end ActionDiagram

namespace InvariantAffineQuotientCover

variable {E : EtaleEquivalenceRelation.{u}} (C : E.InvariantAffineQuotientCover)

/-- Glue the affine quotients of the supplied invariant cover. -/
def schemeQuotient : E.SchemeQuotient :=
  E.schemeQuotientOfInvariantOpenCover C.opens C.isCover C.isInvariant C.hasAffineQuotient

/-- The quotient map supplied by an invariant affine quotient cover is affine. -/
instance : IsAffineHom C.schemeQuotient.q :=
  C.schemeQuotient.isAffineHom_q_of_invariantOpenCover C.opens C.isCover C.isInvariant
    C.isAffine C.hasAffineQuotient

end InvariantAffineQuotientCover

namespace CartesianDiagram.InvariantAffineQuotientCoverModel

variable {I : Type u} [Category.{u} I] {D : I ⥤ EtaleEquivalenceRelation.{u}}
  {c : Cone D} [∀ i, IsAffine (D.obj i).U]
  {K : Type u} [Finite K] {U : K → c.pt.U.Opens}
  (M : CartesianDiagram.InvariantAffineQuotientCoverModel D c U)

/-- A descended cover, pulled back to a further level, as an actual finite cover. -/
def coverAt {j : I} (a : j ⟶ M.index) : (D.obj j).InvariantAffineQuotientCover where
  Index := K
  finite := inferInstance
  opens k := (D.map a).objMap ⁻¹ᵁ M.opens k
  isCover := by
    change (⨆ k, (D.map a).objMap ⁻¹ᵁ M.opens k) = ⊤
    rw [← Scheme.Hom.preimage_iSup, M.isCover, Scheme.Hom.preimage_top]
  isAffine k := (M.isAffine k).preimage _
  isInvariant k := (D.map a).isCartesian.isInvariantOpen_preimage (M.isInvariant k)
  hasAffineQuotient k := (D.map a).isCartesian.hasAffineQuotient_open_preimage
    (M.opens k) (M.isAffine k) (M.hasAffineQuotient k)

end CartesianDiagram.InvariantAffineQuotientCoverModel

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
