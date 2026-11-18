import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Henselian

/-! # Strictly local affine limits of etale neighbourhoods -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Data for a strictly Henselian local affine limit of affine etale
neighbourhoods of a point. Existence and a universal property are not part of
this definition. -/
structure StrictLocalEtaleLimit (S : Scheme.{u}) (s : S) where
  ring : Type u
  [commRing : CommRing ring]
  [henselian : HenselianLocalRing ring]
  [sepClosed : IsSepClosed (IsLocalRing.ResidueField ring)]
  index : Type u
  [category : Category.{u} index]
  [cofiltered : IsCofiltered index]
  diagram : index ⥤ Scheme.{u}
  [affine : ∀ i, IsAffine (diagram.obj i)]
  structural : diagram ⟶ (Functor.const index).obj S
  [etale : ∀ i, Etale (structural.app i)]
  projection : (Functor.const index).obj (Spec (CommRingCat.of ring)) ⟶ diagram
  baseMap : Spec (CommRingCat.of ring) ⟶ S
  compatible : ∀ i, projection.app i ≫ structural.app i = baseMap
  isLimit : IsLimit (Cone.mk (Spec (CommRingCat.of ring)) projection)
  closedPoint_image : baseMap (IsLocalRing.closedPoint ring) = s

attribute [instance] StrictLocalEtaleLimit.commRing StrictLocalEtaleLimit.henselian
  StrictLocalEtaleLimit.sepClosed StrictLocalEtaleLimit.category
  StrictLocalEtaleLimit.cofiltered StrictLocalEtaleLimit.affine
  StrictLocalEtaleLimit.etale

namespace StrictLocalEtaleLimit

variable {S : Scheme.{u}} {s : S} (L : StrictLocalEtaleLimit S s)

/-- The chosen closed point maps to a point over `s` at every affine level. -/
theorem level_point_image (i : L.index) :
    L.structural.app i (L.projection.app i (IsLocalRing.closedPoint L.ring)) = s := by
  have h := congrArg (fun f => f (IsLocalRing.closedPoint L.ring)) (L.compatible i)
  exact h.trans L.closedPoint_image

/-- The actual point at a level, retaining its image in the original base. -/
def levelPoint (i : L.index) : {x : L.diagram.obj i // L.structural.app i x = s} :=
  ⟨L.projection.app i (IsLocalRing.closedPoint L.ring), L.level_point_image i⟩

end StrictLocalEtaleLimit

end Langlands.AlgebraicGeometry
