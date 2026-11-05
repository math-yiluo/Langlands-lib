import Langlands.GroupScheme.Torus.WeilRestrictionCommutative
import Langlands.GroupScheme.GaloisPointRational

/-! # Tensor-unit coordinates for rational Weil-restriction norms -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section Affine

variable (A : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- The tensor-unit model on an affine test algebra, without global-sections factors. -/
def affineUnitsEquiv (R : CommAlgCat A) :
    (groupScheme A B).affinePoints R ≃* (B ⊗[A] R)ˣ :=
  Corepresented.affinePointsEquiv (functor A B) (corepresentableBy A B) R

/-- Change of affine test algebra acts on the right tensor factor. -/
theorem affineUnitsEquiv_naturality {R S : CommAlgCat A} (f : R ⟶ S)
    (x : (groupScheme A B).affinePoints R) :
    affineUnitsEquiv A B S ((algSpec A).map f.op ≫ x) =
      Units.map (Algebra.TensorProduct.lTensor (S := B) B f.hom).toMonoidHom
        (affineUnitsEquiv A B R x) :=
  Corepresented.affinePointsEquiv_naturality (functor A B) (corepresentableBy A B) f x

end Affine

section Field

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (B : Type u) [CommRing B] [Algebra k B] [Module.Finite k B] [Module.Projective k B]

/-- Ground-field points of the actual Weil restriction are the units of its algebra. -/
def rationalUnitsEquiv :
    rationalPoints (groupScheme (CommRingCat.of k) B) ≃* Bˣ :=
  (GaloisPointComparison.rationalCoeffEquiv k (groupScheme (CommRingCat.of k) B)).trans
    ((affineUnitsEquiv (CommRingCat.of k) B (CommAlgCat.of k k)).trans
      (Units.mapEquiv (Algebra.TensorProduct.rid k B B).toMulEquiv))

/-- Points of the actual base change are units of the original tensor algebra. -/
def extensionUnitsEquiv :
    rationalPoints (GaloisPointComparison.baseChanged k L
      (groupScheme (CommRingCat.of k) B)) ≃* (B ⊗[k] L)ˣ :=
  (GaloisPointComparison.baseChangeCoeffEquiv k L
    (groupScheme (CommRingCat.of k) B)).trans
      (affineUnitsEquiv (CommRingCat.of k) B (CommAlgCat.of k L))

/-- Extending a rational point is the inclusion into the left tensor factor. -/
theorem extensionUnitsEquiv_extend (x : rationalPoints (groupScheme (CommRingCat.of k) B)) :
    extensionUnitsEquiv k L B
        (GaloisPointComparison.rationalExtend k L (groupScheme (CommRingCat.of k) B) x) =
      Units.map (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] L).toMonoidHom
        (rationalUnitsEquiv k B x) := by
  change affineUnitsEquiv _ _ _
    (GaloisPointComparison.baseChangeCoeffEquiv _ _ _
      (GaloisPointComparison.rationalExtend _ _ _ x)) = _
  rw [GaloisPointComparison.baseChangeCoeffEquiv_rationalExtend]
  change affineUnitsEquiv _ _ _
    ((algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (Algebra.ofId k L)).op ≫ _) = _
  rw [affineUnitsEquiv_naturality]
  apply Units.ext
  change Algebra.TensorProduct.lTensor (S := B) B (Algebra.ofId k L) _ =
    ((Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] L).comp
      ((Algebra.TensorProduct.rid k B B).toAlgHom.restrictScalars k)) _
  have hmap :
      (Algebra.TensorProduct.lTensor (S := B) B (Algebra.ofId k L)).restrictScalars k =
        (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] L).comp
          ((Algebra.TensorProduct.rid k B B).toAlgHom.restrictScalars k) := by
    ext; simp
  exact DFunLike.congr_fun hmap _

/-- Conjugation acts on the coefficient field in the right tensor factor. -/
theorem extensionUnitsEquiv_conjugate (σ : L ≃ₐ[k] L)
    (x : rationalPoints (GaloisPointComparison.baseChanged k L
      (groupScheme (CommRingCat.of k) B))) :
    extensionUnitsEquiv k L B
        (GaloisPointComparison.rationalConjugate k L
          (groupScheme (CommRingCat.of k) B) σ x) =
      Units.map (Algebra.TensorProduct.lTensor (S := B) B σ.toAlgHom).toMonoidHom
        (extensionUnitsEquiv k L B x) := by
  change affineUnitsEquiv _ _ _
    (GaloisPointComparison.baseChangeCoeffEquiv _ _ _
      (GaloisPointComparison.rationalConjugate _ _ _ σ x)) = _
  rw [GaloisPointComparison.baseChangeCoeffEquiv_rationalConjugate]
  exact affineUnitsEquiv_naturality (CommRingCat.of k) B
    (CommAlgCat.ofHom σ.toAlgHom) _

variable [FiniteDimensional k L] [IsGalois k L]

local instance : IsAffine (commGroupScheme (CommRingCat.of k) B).X.left := by
  change IsAffine (Spec _)
  infer_instance

/-- After tensor inclusion, the descended rational norm is the product of coefficient
conjugates of the tensor unit. -/
theorem rationalNorm_tensor (x : rationalPoints
    ((CommGroupScheme.baseChange (GaloisPointComparison.baseMap k L)).obj
      (commGroupScheme (CommRingCat.of k) B)).toGrp) :
    Units.map (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] L).toMonoidHom
        (rationalUnitsEquiv k B
          (GaloisPointComparison.rationalNorm k L (commGroupScheme (CommRingCat.of k) B) x)) =
      ∏ σ : L ≃ₐ[k] L,
        Units.map (Algebra.TensorProduct.lTensor (S := B) B σ.toAlgHom).toMonoidHom
          (extensionUnitsEquiv k L B x) := by
  let e : rationalPoints
      ((CommGroupScheme.baseChange (GaloisPointComparison.baseMap k L)).obj
        (commGroupScheme (CommRingCat.of k) B)).toGrp ≃* (B ⊗[k] L)ˣ :=
    extensionUnitsEquiv k L B
  have h := congrArg e
    (GaloisPointComparison.rationalExtend_norm k L
      (commGroupScheme (CommRingCat.of k) B) x)
  rw [map_prod] at h
  change extensionUnitsEquiv k L B
    (GaloisPointComparison.rationalExtend k L (groupScheme (CommRingCat.of k) B)
      (GaloisPointComparison.rationalNorm k L (commGroupScheme (CommRingCat.of k) B) x)) =
    _ at h
  rw [extensionUnitsEquiv_extend] at h
  exact h.trans (Finset.prod_congr rfl
    (fun σ _ => extensionUnitsEquiv_conjugate k L B σ x))

end Field

end Langlands.GroupScheme.WeilGm
