import Langlands.GroupScheme.Torus.Weights
import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.SplitExistence.LieWeights

/-! # Character values of base points of `𝔾_m` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- The base point of `𝔾_m` given by a unit of the base field. -/
def gmBasePoint (c : kˣ) : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (Gm (Spec (CommRingCat.of k))).X :=
  (Gm.affinePointsEquiv (𝟙 _)).symm c

/-- Over a `k`-algebra `A`, the base point of `𝔾_m` given by `c` is the unit `c` of `A`. -/
theorem affinePointsEquiv_constantPoint_gmBasePoint (c : kˣ) (A : Type u) [CommRing A]
    [Algebra k A] :
    Gm.affinePointsEquiv
        ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A))).hom
        (GroupScheme.constantPoint (Gm (Spec (CommRingCat.of k))).toGrp (gmBasePoint c)
          ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A)))) =
      Units.map (algebraMap k A).toMonoidHom c := by
  have h := Gm.affinePointsEquiv_naturality (S := Spec (CommRingCat.of k))
    (CommRingCat.ofHom (algebraMap k A)) (𝟙 _) (gmBasePoint c)
  rw [gmBasePoint, MulEquiv.apply_symm_apply] at h
  exact h

/-- The value of the character `t ↦ t ^ m` at the base point `c`, over a `k`-algebra `A`. -/
theorem characterValue_powerHom_constantPoint_gmBasePoint (c : kˣ) (m : ℤ) (A : Type u)
    [CommRing A] [Algebra k A] :
    Lie.characterValue (Gm.powerHom _ m)
        (GroupScheme.constantPoint (Gm (Spec (CommRingCat.of k))).toGrp (gmBasePoint c)
          ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A)))) =
      Units.map (algebraMap k A).toMonoidHom c ^ m := by
  rw [SplitExistence.ChevalleyData.ChevGroup.characterValue_powerHom,
    affinePointsEquiv_constantPoint_gmBasePoint]
  rfl

end Langlands.GroupScheme
