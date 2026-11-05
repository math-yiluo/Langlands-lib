import Langlands.GroupScheme.TensorGaloisPoint
import Langlands.GroupScheme.Lie.BaseChange
import Langlands.GroupScheme.AffineWeilRestriction
import Langlands.GroupScheme.GaloisPointRational

/-! # The actual finite-Galois norm of an affine commutative group scheme -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisNorm

set_option backward.isDefEq.respectTransparency false

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

local notation "T_L" => GaloisPointComparison.baseChanged k L T.toGrp

/-- The tensor-point norm after the actual scheme-base-change comparison. -/
def pointNorm (A : Type u) [CommRing A] [Algebra k A] :
    Lie.AffinePoints T_L (L ⊗[k] A) →* Lie.AffinePoints T.toGrp A :=
  (TensorGaloisPoint.norm k L A T).comp
    (Lie.affineBaseChangeEquiv k L T.toGrp (L ⊗[k] A)).toMonoidHom

/-- The norm on tensor-valued points commutes with every test-algebra map. -/
theorem pointNorm_naturality {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B)
    (x : Lie.AffinePoints T_L (L ⊗[k] A)) :
    pointNorm k L T B
        (Lie.affineMap T_L (Algebra.TensorProduct.lTensor (S := L) L f) x) =
      Lie.affineMap T.toGrp f (pointNorm k L T A x) := by
  change TensorGaloisPoint.norm k L B T
      (Lie.affineBaseChangeEquiv k L T.toGrp (L ⊗[k] B)
        (Lie.affineMap T_L (Algebra.TensorProduct.lTensor (S := L) L f) x)) = _
  rw [Lie.affineBaseChangeEquiv_naturality]
  change TensorGaloisPoint.norm k L B T
      (Lie.affineMap T.toGrp (TensorGaloisPoint.tensorMap k L f)
        (Lie.affineBaseChangeEquiv k L T.toGrp (L ⊗[k] A) x)) = _
  exact (TensorGaloisPoint.norm_naturality k L T f _).symm

/-- The natural group homomorphism from Weil points to target affine coordinates. -/
def normNat :
    AffineWeil.pointFunctor k L T_L ⟶ AffineCoordinates.functor T.toGrp where
  app A := GrpCat.ofHom
    ((CocharacterDatum.toFunctor (Z := T) A).comp (pointNorm k L T A))
  naturality A B f := by
    ext x
    change CocharacterDatum.toFunctor B
        (pointNorm k L T B
          (Lie.affineMap T_L (Algebra.TensorProduct.lTensor (S := L) L f.hom) x)) =
      (AffineCoordinates.functor T.toGrp).map f
        (CocharacterDatum.toFunctor A (pointNorm k L T A x))
    rw [pointNorm_naturality]
    exact CocharacterDatum.toFunctor_naturality f _

variable
  [IsAffine (GaloisPointComparison.baseChanged k L T.toGrp).X.left]
  [LocallyOfFiniteType (GaloisPointComparison.baseChanged k L T.toGrp).X.hom]

/-- The actual algebraic norm `Res_{L/k}(T_L) ⟶ T` over `Spec k`. -/
def norm : AffineWeil.groupScheme k L T_L ⟶ T.toGrp :=
  Corepresented.groupSchemeMap (AffineWeil.corepresentableBy k L T_L)
      (AffineCoordinates.corepresentation T.toGrp) (normNat k L T) ≫
    (AffineCoordinates.groupSchemeIso T.toGrp).hom

/-- On every affine test algebra the morphism is exactly the tensor-point norm. -/
theorem norm_affinePoints (A : Type u) [CommRing A] [Algebra k A]
    (x : (AffineWeil.groupScheme k L T_L).affinePoints (CommAlgCat.of k A)) :
    x ≫ (norm k L T).hom.hom =
      TensorGaloisPoint.norm k L A T
        (Lie.affineBaseChangeEquiv k L T.toGrp (L ⊗[k] A)
          (AffineWeil.pointsEquiv k L T_L A x)) := by
  apply CocharacterDatum.toFunctor_injective (CommAlgCat.of k A)
  rw [norm, Grp.comp_hom_hom, ← Category.assoc,
    CocharacterDatum.toFunctor_comp_hom, Corepresented.groupSchemeMap_affinePoints]
  rfl

end Langlands.GroupScheme.GaloisNorm
