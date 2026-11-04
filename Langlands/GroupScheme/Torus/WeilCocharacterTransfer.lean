import Langlands.GroupScheme.TensorGaloisPoint
import Langlands.GroupScheme.Lie.BaseChange
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterWeights
import Langlands.GroupScheme.Torus.WeilRestrictionSeparable

/-! # Transfer of a cocharacter from a finite Galois extension -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (Z : CommGroupScheme (Spec (CommRingCat.of k)))

local notation "Z_K" =>
  Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) Z.toGrp


/-- Evaluate a cocharacter over the extension and view its value in the original group. -/
def cocharacterValue (nu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ Z_K) (A : Type u) [CommRing A] [Algebra k A] [Algebra K A]
    [IsScalarTower k K A] : Aˣ →* Lie.AffinePoints Z.toGrp A :=
  (Lie.affineBaseChangeEquiv k K Z.toGrp A).toMonoidHom.comp
    ((GroupScheme.affinePointsTarget _ nu (CommAlgCat.of K A)).comp
      (Gm.algebraPointsEquiv (R := CommRingCat.of K) A).symm.toMonoidHom)

theorem cocharacterValue_naturality (nu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ Z_K) {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    [Algebra k B] [Algebra K B] [IsScalarTower k K B]
    (f : A →ₐ[K] B) (x : Aˣ) :
    cocharacterValue k K Z nu B (Units.map f.toMonoidHom x) =
      Lie.affineMap Z.toGrp (f.restrictScalars k) (cocharacterValue k K Z nu A x) := by
  change Lie.affineBaseChangeEquiv k K Z.toGrp B
      ((Gm.algebraPointsEquiv B).symm (Units.map f.toMonoidHom x) ≫ nu.hom.hom) = _
  rw [Gm.algebraPointsEquiv_symm_naturality, Lie.affineMap_apply, Category.assoc]
  exact Lie.affineBaseChangeEquiv_naturality k K Z.toGrp f _

variable [FiniteDimensional k K] [IsGalois k K] [IsAffine Z.X.left]

/-- Norm of the value of the extension-field cocharacter on a tensor unit. -/
def transferPoint (nu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ Z_K) (A : Type u) [CommRing A] [Algebra k A] :
    (K ⊗[k] A)ˣ →* Lie.AffinePoints Z.toGrp A :=
  (TensorGaloisPoint.norm k K A Z).comp (cocharacterValue k K Z nu (K ⊗[k] A))

theorem transferPoint_naturality (nu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ Z_K) {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) (x : (K ⊗[k] A)ˣ) :
    transferPoint k K Z nu B
        (Units.map (TensorGaloisPoint.tensorMap k K f).toMonoidHom x) =
      Lie.affineMap Z.toGrp f (transferPoint k K Z nu A x) := by
  change TensorGaloisPoint.norm k K B Z
      (cocharacterValue k K Z nu (K ⊗[k] B)
        (Units.map (TensorGaloisPoint.tensorMap k K f).toMonoidHom x)) = _
  have hn := cocharacterValue_naturality k K Z nu
    (Algebra.TensorProduct.lTensor (S := K) K f) x
  change cocharacterValue k K Z nu (K ⊗[k] B)
      (Units.map (TensorGaloisPoint.tensorMap k K f).toMonoidHom x) =
    Lie.affineMap Z.toGrp (TensorGaloisPoint.tensorMap k K f)
      (cocharacterValue k K Z nu (K ⊗[k] A) x) at hn
  rw [hn, ← TensorGaloisPoint.norm_naturality]
  rfl

/-- A natural homomorphism from the Weil-restriction point functor to affine coordinates. -/
def transferNat (nu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ Z_K) :
    functor (CommRingCat.of k) K ⟶ AffineCoordinates.functor Z.toGrp where
  app A := GrpCat.ofHom
    ((CocharacterDatum.toFunctor (Z := Z) A).comp (transferPoint k K Z nu A))
  naturality A B f := by
    ext x
    change CocharacterDatum.toFunctor B
      (transferPoint k K Z nu B
        (Units.map (TensorGaloisPoint.tensorMap k K f.hom).toMonoidHom x)) =
      (AffineCoordinates.functor Z.toGrp).map f
        (CocharacterDatum.toFunctor A (transferPoint k K Z nu A x))
    rw [transferPoint_naturality]
    exact CocharacterDatum.toFunctor_naturality f _

/-- The actual homomorphism from `Res_{K/k} Gm` obtained by cocharacter evaluation and norm. -/
def cocharacterTransfer (nu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ Z_K) : groupScheme (CommRingCat.of k) K ⟶ Z.toGrp :=
  Corepresented.groupSchemeMap (corepresentableBy (CommRingCat.of k) K)
      (AffineCoordinates.corepresentation Z.toGrp) (transferNat k K Z nu) ≫
    (AffineCoordinates.groupSchemeIso Z.toGrp).hom

/-- The transfer on every affine test algebra is exactly cocharacter evaluation and norm. -/
theorem cocharacterTransfer_affinePoints (nu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ Z_K) (A : CommAlgCat (CommRingCat.of k))
    (x : GroupScheme.affinePoints (groupScheme (CommRingCat.of k) K) A) :
    x ≫ (cocharacterTransfer k K Z nu).hom.hom =
      transferPoint k K Z nu A
        (Corepresented.affinePointsEquiv _ (corepresentableBy (CommRingCat.of k) K) A x) := by
  apply CocharacterDatum.toFunctor_injective A
  rw [cocharacterTransfer, Grp.comp_hom_hom, ← Category.assoc,
    CocharacterDatum.toFunctor_comp_hom, Corepresented.groupSchemeMap_affinePoints]
  rfl

end Langlands.GroupScheme.WeilGm
