import Langlands.GroupScheme.Absolute.DynamicParabolicRecognition
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Rational.AffineGeometricUnipotentRadical
import Langlands.GroupScheme.Rational.DynamicSemistandardIntersectionModels
import Langlands.GroupScheme.Rational.ElementarySubgroup

/-! # Contracting rational points in the actual parabolic elementary subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A rational point contracting under an actual ground-field cocharacter is
in the image of an actual geometric parabolic radical. -/
theorem mem_parabolicUnipotentPointSet_of_dynamicUnipotent
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {x : rationalPoints G}
    (hx : x ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))) :
    x ∈ parabolicUnipotentPointSet G := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let hP := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  let hU := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  let r := Dynamic.unipotentToParabolic hP hU
  have hcomp : r ≫ Dynamic.Affine.parabolicHom χ = Dynamic.Affine.unipotentHom χ :=
    Dynamic.unipotentToParabolic_comp hP hU
  have hUr : (Dynamic.unipotent χ).IsRepresentedBy
      (r ≫ Dynamic.Affine.parabolicHom χ) := by
    rw [hcomp]
    exact hU
  have hp := isParabolicSubgroup_of_range_eq_dynamicParabolic hG
    (Dynamic.Affine.parabolicHom χ)
    (Dynamic.Affine.isClosedSubgroup_parabolicHom χ) χ hP.2
  have hr := dynamicGeometricUnipotentRadical k G hG χ
    (Dynamic.Affine.parabolicScheme χ) (Dynamic.Affine.unipotentScheme χ)
    (Dynamic.Affine.parabolicHom χ) r hP hUr
  let : IsAffineHom (Dynamic.Affine.parabolicScheme χ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_parabolicHom χ).isAffineHom
  refine ⟨Dynamic.Affine.parabolicScheme χ, Dynamic.Affine.unipotentScheme χ,
    Dynamic.Affine.parabolicHom χ, r, hp, hr.leviSubgroup, ?_⟩
  change x ∈ (SubgroupFunctor.range (r ≫ Dynamic.Affine.parabolicHom χ)).carrier
    (Over.mk (𝟙 _))
  rw [hUr.2]
  exact hx

/-- Every actual rational identity-limit subgroup lies in the subgroup generated
by actual rational parabolic radicals of a connected reductive group. -/
theorem dynamicUnipotent_le_parabolicElementarySubgroup
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) ≤
      parabolicElementarySubgroup G := by
  intro x hx
  exact Subgroup.subset_closure
    (mem_parabolicUnipotentPointSet_of_dynamicUnipotent hG χ hx)

/-- The original inclusion of contracting rational points with its codomain
restricted to the actual parabolic elementary subgroup. -/
def dynamicUnipotentPointsToParabolicElementarySubgroup
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) →*
      parabolicElementarySubgroup G :=
  Subgroup.inclusion (dynamicUnipotent_le_parabolicElementarySubgroup hG χ)

@[simp]
theorem dynamicUnipotentPointsToParabolicElementarySubgroup_apply_coe
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (x : (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))) :
    (dynamicUnipotentPointsToParabolicElementarySubgroup hG χ x :
      rationalPoints G) = x.val := rfl

/-- Any actual source homomorphism takes contracting rational points into the
target's actual parabolic elementary subgroup. Only the target is reductive. -/
theorem map_dynamicUnipotent_le_parabolicElementarySubgroup
    (hG : IsConnectedReductive G) (f : H ⟶ G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ H) :
    ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))).map (rationalPoints.map f) ≤
      parabolicElementarySubgroup G := by
  rintro _ ⟨x, hx, rfl⟩
  exact dynamicUnipotent_le_parabolicElementarySubgroup hG (χ ≫ f)
    (Dynamic.unipotent_le_comap χ f _ hx)

end Langlands.GroupScheme
