import Langlands.AlgebraicGeometry.ComponentConstantMaps
import Langlands.GroupScheme.AlgebraicallyClosedComponentProof

/-! # Algebraizing componentwise constant functions on rational sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Langlands.GroupScheme.IdentityComponent (basePoint)

namespace Langlands.AlgebraicGeometry.ComponentConstant

variable {k : Type u} [Field k]
  (X : Over (Spec (CommRingCat.of k))) {Y : Over (Spec (CommRingCat.of k))}

/-- The actual connected component containing a rational section. -/
def sectionComponent (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    _root_.ConnectedComponents X.left :=
  _root_.ConnectedComponents.mk (x.left (basePoint k))

/-- A componentwise constant map has its prescribed value on every rational section. -/
theorem section_comp_ofComponents [IsLocallyNoetherian X.left]
    (s : _root_.ConnectedComponents X.left →
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Y))
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    x ≫ ofComponents X s = s (sectionComponent X x) := by
  let : IsLocallyNoetherian (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of k)))
  have hf : (fun c => s (componentMap x.left c)) =
      fun _ => s (sectionComponent X x) := by
    funext c
    obtain ⟨p, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    rw [componentMap_mk]
    congr 1
    exact congrArg (fun t => _root_.ConnectedComponents.mk (x.left t))
      (@Subsingleton.elim (Spec (CommRingCat.of k)) _ p (basePoint k))
  rw [precomp_ofComponents x s, hf, ofComponents_const]
  rw [show toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ from
    toUnit_unique _ _, Category.id_comp]

variable [IsAlgClosed k] [LocallyOfFiniteType X.hom]

local instance : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- Every actual component of a locally finite type scheme over an algebraically
closed field contains a rational section. -/
theorem sectionComponent_surjective : Function.Surjective (sectionComponent X) := by
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  intro c
  obtain ⟨p, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
  obtain ⟨q, hqp, hq⟩ := nonempty_inter_closedPoints
    (show (connectedComponent p).Nonempty from ⟨p, mem_connectedComponent⟩)
    isClosed_connectedComponent.isLocallyClosed
  change IsClosed ({q} : Set X.left) at hq
  refine ⟨Over.homMk (pointOfClosedPoint X.hom q hq)
    (pointOfClosedPoint_comp X.hom q hq), ?_⟩
  change _root_.ConnectedComponents.mk
    (pointOfClosedPoint X.hom q hq (basePoint k)) =
      _root_.ConnectedComponents.mk p
  rw [pointOfClosedPoint_apply]
  exact _root_.ConnectedComponents.coe_eq_coe'.mpr hqp

/-- A chosen rational representative of every actual component. -/
def representative (c : _root_.ConnectedComponents X.left) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X :=
  (sectionComponent_surjective X c).choose

@[simp] theorem sectionComponent_representative
    (c : _root_.ConnectedComponents X.left) :
    sectionComponent X (representative X c) = c :=
  (sectionComponent_surjective X c).choose_spec

/-- Rational sections detect equality between componentwise constant morphisms,
including when the source has nilpotents. -/
theorem IsComponentConstant.hom_ext {f g : X ⟶ Y}
    (hf : IsComponentConstant X f) (hg : IsComponentConstant X g)
    (h : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X, x ≫ f = x ≫ g) :
    f = g := by
  obtain ⟨s, rfl⟩ := hf
  obtain ⟨t, rfl⟩ := hg
  congr 1
  funext c
  have hc := h (representative X c)
  simpa only [section_comp_ofComponents, sectionComponent_representative] using hc

/-- Algebraize a function on rational sections that is constant on actual components. -/
def ofRationalFunction
    (f : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) →
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Y)) : X ⟶ Y :=
  ofComponents X (fun c => f (representative X c))

theorem ofRationalFunction_isComponentConstant
    (f : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) →
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Y)) :
    IsComponentConstant X (ofRationalFunction X f) :=
  ⟨_, rfl⟩

/-- Component constancy makes the algebraized function agree with the given
function on every rational section. -/
theorem section_comp_ofRationalFunction
    (f : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) →
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Y))
    (hf : ∀ x y, sectionComponent X x = sectionComponent X y → f x = f y)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    x ≫ ofRationalFunction X f = f x := by
  rw [ofRationalFunction, section_comp_ofComponents]
  exact hf _ _ (sectionComponent_representative X _)

end Langlands.AlgebraicGeometry.ComponentConstant
