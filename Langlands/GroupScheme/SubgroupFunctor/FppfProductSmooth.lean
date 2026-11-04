import Langlands.GroupScheme.SubgroupFunctor.FppfProductGeometry
import Langlands.GroupScheme.SmoothProducts
import Langlands.AlgebraicGeometry.GeometricallyReducedImage
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Mathlib.AlgebraicGeometry.Group.Smooth

/-! # Smoothness of represented fppf products over a field -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- An affine group of locally finite type over a field is smooth if it
receives an epimorphism from a smooth affine scheme over that field. -/
theorem smooth_of_epi_from_smooth
    {P : GroupScheme (Spec (CommRingCat.of k))}
    {V : Over (Spec (CommRingCat.of k))} (q : V ⟶ P.X)
    [IsAffineHom V.hom] [Smooth V.hom]
    [IsAffineHom P.X.hom] [LocallyOfFiniteType P.X.hom] [Epi q.left] :
    Smooth P.X.hom := by
  let : IsAffine V.left := isAffine_of_isAffineHom V.hom
  let : IsAffine P.X.left := isAffine_of_isAffineHom P.X.hom
  let : GeometricallyReduced V.hom :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth V.hom
  let : GeometricallyReduced (q.left ≫ P.X.hom) := by
    rw [Over.w q]
    infer_instance
  let : GeometricallyReduced P.X.hom :=
    Langlands.SchemeImageGeometry.geometricallyReduced_of_epi q.left P.X.hom
  let : GrpObj (Over.mk P.X.hom) := P.grp
  exact AlgebraicGeometry.smooth_of_grpObj P.X.hom

namespace SubgroupFunctor.IsFppfProduct

variable {G H N P : GroupScheme (Spec (CommRingCat.of k))}
    {F U : SubgroupFunctor G} {i : P ⟶ G} {j : H ⟶ G} {l : N ⟶ G}

set_option backward.isDefEq.respectTransparency.types false in
/-- A represented fppf product of smooth affine factors is smooth, provided
its actual group representative is affine and locally of finite type. -/
theorem smooth (hi : IsFppfProduct F U i)
    (hH : F.IsRepresentedBy j) (hN : U.IsRepresentedBy l)
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    [Smooth N.X.hom] [IsAffineHom N.X.hom]
    [IsAffineHom P.X.hom] [LocallyOfFiniteType P.X.hom] :
    Smooth P.X.hom := by
  let : Smooth (H.X ⊗ N.X).hom :=
    smooth_tensor H.X N.X inferInstance inferInstance
  let : IsAffineHom (H.X ⊗ N.X).hom := by
    change IsAffineHom
      (CategoryTheory.Limits.pullback.fst H.X.hom N.X.hom ≫ H.X.hom)
    let : IsAffineHom (CategoryTheory.Limits.pullback.fst H.X.hom N.X.hom) :=
      MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom N.X.hom)
    infer_instance
  let : Epi (productMul hi hH hN).left := hi.epi_productMul hH hN
  exact smooth_of_epi_from_smooth (productMul hi hH hN)

end SubgroupFunctor.IsFppfProduct

end Langlands.GroupScheme
