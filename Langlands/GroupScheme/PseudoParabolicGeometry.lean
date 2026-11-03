import Langlands.GroupScheme.PseudoParabolicStructureStatement
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.SubgroupFunctor.FppfProductGeometry
import Langlands.AlgebraicGeometry.GeometricallyReducedImage
import Langlands.AlgebraicGeometry.SmoothGeometricallyReducedProof
import Mathlib.AlgebraicGeometry.Group.Smooth

/-! # Geometry of the supplied pseudo-parabolic subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A finite type group over a field is smooth if it is an affine epimorphic
image of a geometrically reduced scheme. -/
theorem smooth_of_affine_epi
    (P : GroupScheme (Spec (CommRingCat.of k))) {X : Scheme.{u}}
    [IsAffine X] [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
    (m : X ⟶ P.X.left) [Epi m] [GeometricallyReduced (m ≫ P.X.hom)] :
    Smooth P.X.hom := by
  let : GeometricallyReduced P.X.hom :=
    SchemeImageGeometry.geometricallyReduced_of_epi m P.X.hom
  let : GrpObj (Over.mk P.X.hom) := P.grp
  exact AlgebraicGeometry.smooth_of_grpObj P.X.hom

set_option backward.isDefEq.respectTransparency.types false in
/-- A group locally of finite type over a field is smooth if its underlying scheme
is the epimorphic image of a product of smooth affine groups. -/
theorem smooth_of_product_epi
    (H U P : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [Smooth U.X.hom]
    [IsAffineHom H.X.hom] [IsAffineHom U.X.hom]
    [IsAffineHom P.X.hom] [LocallyOfFiniteType P.X.hom]
    (m : H.X ⊗ U.X ⟶ P.X) [Epi m.left] : Smooth P.X.hom := by
  have hprodSmooth : Smooth (H.X ⊗ U.X).hom := by
    change Smooth (pullback.fst H.X.hom U.X.hom ≫ H.X.hom)
    infer_instance
  have hprodAffine : IsAffineHom (H.X ⊗ U.X).hom := by
    change IsAffineHom (pullback.fst H.X.hom U.X.hom ≫ H.X.hom)
    let : IsAffineHom (pullback.fst H.X.hom U.X.hom) :=
      MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom U.X.hom)
    infer_instance
  let : IsAffine (H.X ⊗ U.X).left := isAffine_of_isAffineHom (H.X ⊗ U.X).hom
  let : IsAffine P.X.left := isAffine_of_isAffineHom P.X.hom
  have : Smooth (m.left ≫ P.X.hom) := by
    rw [m.w]
    exact hprodSmooth
  let : GeometricallyReduced (m.left ≫ P.X.hom) :=
    Langlands.AlgebraicGeometry.smoothGeometricallyReduced _ _ _ inferInstance
  exact smooth_of_affine_epi P m.left

/-- An ordered product of smooth affine groups mapping epimorphically and
surjectively onto the supplied group scheme. The map is a scheme morphism over
the field; it need not be a group homomorphism. -/
structure SmoothAffineProductPresentation
    (P : GroupScheme (Spec (CommRingCat.of k))) where
  leftFactor : GroupScheme (Spec (CommRingCat.of k))
  rightFactor : GroupScheme (Spec (CommRingCat.of k))
  smooth_left : Smooth leftFactor.X.hom
  smooth_right : Smooth rightFactor.X.hom
  affine_left : IsAffineHom leftFactor.X.hom
  affine_right : IsAffineHom rightFactor.X.hom
  mul : leftFactor.X ⊗ rightFactor.X ⟶ P.X
  epi_mul : Epi mul.left
  surjective_mul : Surjective mul.left

/-- A group locally of finite type with an affine structure map is smooth
whenever it has a smooth affine product presentation. -/
theorem SmoothAffineProductPresentation.smooth
    {P : GroupScheme (Spec (CommRingCat.of k))}
    (q : SmoothAffineProductPresentation P)
    [IsAffineHom P.X.hom] [LocallyOfFiniteType P.X.hom] : Smooth P.X.hom := by
  let : Smooth q.leftFactor.X.hom := q.smooth_left
  let : Smooth q.rightFactor.X.hom := q.smooth_right
  let : IsAffineHom q.leftFactor.X.hom := q.affine_left
  let : IsAffineHom q.rightFactor.X.hom := q.affine_right
  let : Epi q.mul.left := q.epi_mul
  exact smooth_of_product_epi q.leftFactor q.rightFactor P q.mul

namespace IsPseudoParabolicSubgroup

variable {G P : GroupScheme (Spec (CommRingCat.of k))} {i : P ⟶ G}

/-- The structure morphism of the supplied pseudo-parabolic source is affine. -/
theorem source_isAffineHom (hi : IsPseudoParabolicSubgroup i) : IsAffineHom P.X.hom := by
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : IsAffineHom G.X.hom := hi.isAffineHom
  rw [← i.hom.hom.w]
  infer_instance

/-- The supplied pseudo-parabolic source is locally of finite type over the field. -/
theorem source_locallyOfFiniteType (hi : IsPseudoParabolicSubgroup i) :
    LocallyOfFiniteType P.X.hom := by
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : Smooth G.X.hom := hi.smooth
  rw [← i.hom.hom.w]
  infer_instance

private theorem nonempty_smoothAffineProductPresentation
    (hi : IsPseudoParabolicSubgroup i) : Nonempty (SmoothAffineProductPresentation P) := by
  let : Smooth G.X.hom := hi.smooth
  let : IsAffineHom G.X.hom := hi.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨U, j, χ, hj, hprod⟩ := hi.presentation
  let H := Dynamic.Affine.parabolicScheme χ
  let h := Dynamic.Affine.parabolicHom χ
  have hH : (Dynamic.parabolic χ).IsRepresentedBy h :=
    Dynamic.Affine.isRepresentedBy_parabolicHom χ
  let : IsClosedImmersion h.hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_parabolicHom χ
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  have hU : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hHaff : IsAffineHom H.X.hom := by
    rw [← h.hom.hom.w]
    infer_instance
  have hUaff : IsAffineHom U.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  exact ⟨{
    leftFactor := H
    rightFactor := U
    smooth_left := (dynamicSmooth k G χ H h).1 hH
    smooth_right := hj.smooth
    affine_left := hHaff
    affine_right := hUaff
    mul := hprod.productMul hH hU
    epi_mul := hprod.epi_productMul hH hU
    surjective_mul := hprod.surjective_productMul hH hU }⟩

/-- Choose a smooth affine product presentation of the actual source of the
pseudo-parabolic inclusion. -/
def smoothAffineProductPresentation (hi : IsPseudoParabolicSubgroup i) :
    SmoothAffineProductPresentation P :=
  Classical.choice (nonempty_smoothAffineProductPresentation hi)

/-- The supplied pseudo-parabolic source is smooth over the ground field. -/
theorem source_smooth (hi : IsPseudoParabolicSubgroup i) : Smooth P.X.hom := by
  let : IsAffineHom P.X.hom := hi.source_isAffineHom
  let : LocallyOfFiniteType P.X.hom := hi.source_locallyOfFiniteType
  exact hi.smoothAffineProductPresentation.smooth

end IsPseudoParabolicSubgroup

end Langlands.GroupScheme
