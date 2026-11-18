import Langlands.GroupScheme.Descent.Refinement
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Base change of Čech overlaps of a scheme morphism -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.CechBaseChange

variable {B S C V : Scheme.{u}} {p : S ⟶ B} {t : V ⟶ C} {q : V ⟶ S} {b : C ⟶ B}

/-- The map of double overlaps induced by a commuting square of scheme morphisms. -/
def overlapMap (w : q ≫ p = t ≫ b) : Overlap t ⟶ Overlap p :=
  pullback.map t t p p q q b w.symm w.symm

@[reassoc (attr := simp)] theorem overlapMap_fst (w : q ≫ p = t ≫ b) :
    overlapMap w ≫ fst p = fst t ≫ q := by
  simp [overlapMap]

@[reassoc (attr := simp)] theorem overlapMap_snd (w : q ≫ p = t ≫ b) :
    overlapMap w ≫ snd p = snd t ≫ q := by
  simp [overlapMap]

/-- A square extending a pullback by pulling its vertical arrow back along a second arrow. -/
private theorem isPullback_map_fst {X Y Z X₀ Y₀ Z₀ : Scheme.{u}}
    {f₀ : X₀ ⟶ Z₀} {g₀ : Y₀ ⟶ Z₀} {f : X ⟶ Z} {g : Y ⟶ Z}
    {x : X₀ ⟶ X} {y : Y₀ ⟶ Y} {z : Z₀ ⟶ Z}
    (hx : x ≫ f = f₀ ≫ z) (hy : IsPullback y g₀ g z) :
    IsPullback (pullback.map f₀ g₀ f g x y z hx.symm hy.w.symm)
      (pullback.fst f₀ g₀) (pullback.fst f g) x := by
  have ho : IsPullback (pullback.map f₀ g₀ f g x y z hx.symm hy.w.symm ≫ pullback.snd f g)
      (pullback.fst f₀ g₀) g (x ≫ f) := by
    rw [pullback.map, pullback.lift_snd, hx]
    exact ((IsPullback.of_hasPullback f₀ g₀).paste_vert hy.flip).flip
  exact ho.of_right (by simp) (IsPullback.of_hasPullback f g).flip

/-- For a cartesian square of covers, the map of double overlaps is a pullback of
its map on the sources along the first projection. -/
theorem overlapMap_isPullback (h : IsPullback q t p b) :
    IsPullback (overlapMap h.w) (fst t) (fst p) q :=
  isPullback_map_fst h.w h

/-- The map of triple overlaps induced by a commuting square of cover morphisms. -/
def tripleMap (w : q ≫ p = t ≫ b) : Triple t ⟶ Triple p :=
  pullback.map (snd t) (fst t) (snd p) (fst p) (overlapMap w) (overlapMap w) q
    (overlapMap_snd w).symm (overlapMap_fst w).symm

@[reassoc (attr := simp)] theorem tripleMap_p12 (w : q ≫ p = t ≫ b) :
    tripleMap w ≫ p12 p = p12 t ≫ overlapMap w := by
  simp [tripleMap]

@[reassoc (attr := simp)] theorem tripleMap_p23 (w : q ≫ p = t ≫ b) :
    tripleMap w ≫ p23 p = p23 t ≫ overlapMap w := by
  simp [tripleMap]

@[reassoc (attr := simp)] theorem tripleMap_p1 (w : q ≫ p = t ≫ b) :
    tripleMap w ≫ p1 p = p1 t ≫ q := by
  simp [p1]

@[reassoc (attr := simp)] theorem tripleMap_p2 (w : q ≫ p = t ≫ b) :
    tripleMap w ≫ p2 p = p2 t ≫ q := by
  simp [p2]

@[reassoc (attr := simp)] theorem tripleMap_p3 (w : q ≫ p = t ≫ b) :
    tripleMap w ≫ p3 p = p3 t ≫ q := by
  simp [p3]

@[reassoc (attr := simp)] theorem tripleMap_p13 (w : q ≫ p = t ≫ b) :
    tripleMap w ≫ p13 p = p13 t ≫ overlapMap w := by
  apply pullback.hom_ext <;> simp

/-- For a cartesian square of covers, the map of triple overlaps is a pullback of
its map of double overlaps along the projection to the first two coordinates. -/
theorem tripleMap_isPullback (h : IsPullback q t p b) :
    IsPullback (tripleMap h.w) (p12 t) (p12 p) (overlapMap h.w) :=
  isPullback_map_fst (overlapMap_snd h.w) (overlapMap_isPullback h)

/-- A surjective closed immersion induces a homeomorphism on underlying spaces. -/
theorem isHomeomorph_of_closedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] [Surjective f] : IsHomeomorph f :=
  isHomeomorph_iff_isEmbedding_surjective.mpr ⟨f.isClosedEmbedding.isEmbedding, f.surjective⟩

end Langlands.GroupScheme.Descent.CechBaseChange
