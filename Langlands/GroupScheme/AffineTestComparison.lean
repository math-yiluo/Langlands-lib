import Langlands.GroupScheme.Multiplicative

set_option maxHeartbeats 100000
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj TensorProduct Classical

namespace Langlands.GroupScheme.Gm
universe u

/-! # Canonical comparisons of affine test objects and their unit points -/

/-- Equal affine structure maps give an isomorphism with identity underlying maps. -/
def affineTestIso {S : Scheme.{u}} {B : CommRingCat.{u}}
    (f g : Spec B ⟶ S) (h : f = g) : Over.mk f ≅ Over.mk g where
  hom := Over.homMk (𝟙 _) (by simpa using h.symm)
  inv := Over.homMk (𝟙 _) (by simpa using h)
  hom_inv_id := by apply Over.OverMorphism.ext; exact Category.id_comp _
  inv_hom_id := by apply Over.OverMorphism.ext; exact Category.id_comp _

/-- This isomorphism has the identity underlying scheme morphism. -/
theorem affineTestIso_hom_left {S : Scheme.{u}} {B : CommRingCat.{u}}
    (f g : Spec B ⟶ S) (h : f = g) :
    (affineTestIso f g h).hom.left = 𝟙 _ := rfl

theorem affinePointsEquiv_iso {S : Scheme.{u}} {B : CommRingCat.{u}}
    (f g : Spec B ⟶ S) (h : f = g) (v : Bˣ) :
    (affinePointsEquiv f).symm v =
      (affineTestIso f g h).hom ≫ (affinePointsEquiv g).symm v := by
  apply (affinePointsEquiv f).injective
  rw [MulEquiv.apply_symm_apply]
  apply Units.ext
  rw [affinePointsEquiv_val, pointsEquiv_naturality, affineTestIso_hom_left]
  change (v : B) = (affinePointsEquiv g ((affinePointsEquiv g).symm v) : B)
  rw [MulEquiv.apply_symm_apply]

/-- Identity-map comparison for the spectrum of a bundled ring. -/
def specIdentityTestIso (B : CommRingCat.{u}) :
    Over.mk (Spec.map (𝟙 B)) ≅ Over.mk (𝟙 (Spec B)) :=
  affineTestIso _ _ (Spec.map_id B)

/-- The underlying unit point is the canonical pullback lift. -/
theorem affinePointsEquiv_symm_left {S : Scheme.{u}} {B : CommRingCat.{u}}
    (f : Spec B ⟶ S) (v : Bˣ) :
    ((affinePointsEquiv f).symm v).left =
      Limits.pullback.lift
        ((unitsHomEquiv (Spec B)).symm
          (Units.map (Scheme.ΓSpecIso B).inv.hom.toMonoidHom v)) f
        (specULiftZIsTerminal.hom_ext _ _) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Unit points agree on the two canonical identity tests. -/
theorem specIdentityTestIso_unit_left (B : CommRingCat.{u}) (v : Bˣ) :
    ((affinePointsEquiv (Spec.map (𝟙 B))).symm v).left =
      ((affinePointsEquiv (𝟙 (Spec B))).symm v).left := by
  simp only [affinePointsEquiv_symm_left, Spec.map_id]

end Langlands.GroupScheme.Gm
