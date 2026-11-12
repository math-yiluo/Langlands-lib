import Langlands.AlgebraicGeometry.AlgebraicSpace.SpacePoints

/-! # Comparison of represented presheaf points with scheme points -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry IsLocalRing

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace FieldPoint

/-- The underlying scheme point of a field-valued point of a represented presheaf. -/
def schemeValue {U : Over S} (p : FieldPoint ((schemeYoneda S).obj U)) : U.left :=
  p.val.down.left (closedPoint p.field)

/-- Agreement after field extension implies equality of the underlying scheme points. -/
theorem schemeValue_eq_of_rel {U : Over S}
    {p q : FieldPoint ((schemeYoneda S).obj U)}
    (h : Rel ((schemeYoneda S).obj U) p q) : p.schemeValue = q.schemeValue := by
  obtain ⟨Ω, _, i, j, hb, he⟩ := h
  have hv := congrArg (fun z => z.down.left (closedPoint Ω)) he
  change p.val.down.left ((Spec.map (CommRingCat.ofHom i)) (closedPoint Ω)) =
    q.val.down.left ((Spec.map (CommRingCat.ofHom j)) (closedPoint Ω)) at hv
  simpa only [schemeValue, Subsingleton.elim ((Spec.map (CommRingCat.ofHom i)) (closedPoint Ω))
    (closedPoint p.field), Subsingleton.elim
      ((Spec.map (CommRingCat.ofHom j)) (closedPoint Ω)) (closedPoint q.field)] using hv

end FieldPoint

/-- A point of a represented presheaf determines an ordinary point of its representing scheme. -/
def schemePointsTo (U : Over S) : Points ((schemeYoneda S).obj U) → U.left :=
  Quot.lift FieldPoint.schemeValue (fun _ _ h => FieldPoint.schemeValue_eq_of_rel h)

@[simp]
theorem schemePointsTo_schemePoint (U : Over S) (x : U.left) :
    schemePointsTo U (schemePoint U x) = x := by
  exact Scheme.fromSpecResidueField_apply _ _

/-- Every field-valued point represents the canonical residue-field point at its image. -/
theorem schemePoint_schemeValue {U : Over S}
    (p : FieldPoint ((schemeYoneda S).obj U)) :
    schemePoint U p.schemeValue = Quot.mk _ p := by
  let f := p.val.down.left
  let i := (Scheme.descResidueField (Scheme.stalkClosedPointTo f)).hom
  have hi : Spec.map (CommRingCat.ofHom i) ≫ U.left.fromSpecResidueField p.schemeValue = f :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField p.field U.left f
  apply Quot.sound
  refine ⟨p.field, inferInstance, i, RingHom.id _, ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom (RingHom.id p.field)) ≫ p.base =
      Spec.map (CommRingCat.ofHom i) ≫ (U.left.fromSpecResidueField p.schemeValue ≫ U.hom)
    have hid : Spec.map (CommRingCat.ofHom (RingHom.id p.field)) = 𝟙 _ := Spec.map_id _
    rw [hid, Category.id_comp, ← Category.assoc, hi]
    exact (Over.w p.val.down).symm
  · apply ULift.ext
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom i) ≫ U.left.fromSpecResidueField p.schemeValue =
      Spec.map (CommRingCat.ofHom (RingHom.id p.field)) ≫ f
    have hid : Spec.map (CommRingCat.ofHom (RingHom.id p.field)) = 𝟙 _ := Spec.map_id _
    rw [hid, Category.id_comp]
    exact hi

@[simp]
theorem schemePoint_schemePointsTo (U : Over S)
    (x : Points ((schemeYoneda S).obj U)) :
    schemePoint U (schemePointsTo U x) = x := by
  induction x using Quot.ind
  exact schemePoint_schemeValue _

/-- Points of the presheaf represented by a scheme are the ordinary scheme points. -/
def schemePointsEquiv (U : Over S) : Points ((schemeYoneda S).obj U) ≃ U.left where
  toFun := schemePointsTo U
  invFun := schemePoint U
  left_inv := schemePoint_schemePointsTo U
  right_inv := schemePointsTo_schemePoint U

/-- The comparison with ordinary scheme points is natural in scheme morphisms. -/
@[simp]
theorem schemePointsTo_map {U V : Over S} (g : U ⟶ V)
    (x : Points ((schemeYoneda S).obj U)) :
    schemePointsTo V (Points.map ((schemeYoneda S).map g) x) =
      g.left (schemePointsTo U x) := by
  induction x using Quot.ind
  rfl

/-- Canonical residue-field points are natural in scheme morphisms. -/
@[simp]
theorem schemePoint_naturality {U V : Over S} (g : U ⟶ V) (x : U.left) :
    Points.map ((schemeYoneda S).map g) (schemePoint U x) = schemePoint V (g.left x) := by
  apply (schemePointsEquiv V).injective
  simp only [schemePointsEquiv, Equiv.coe_fn_mk, schemePointsTo_map,
    schemePointsTo_schemePoint]

end Langlands.AlgebraicGeometry.AlgebraicSpace
