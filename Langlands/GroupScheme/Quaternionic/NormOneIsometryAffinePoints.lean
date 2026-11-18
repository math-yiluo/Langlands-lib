import Langlands.GroupScheme.Quaternionic.NormOneIsometry

/-! # Affine tensor coordinates on the actual norm-one isometry kernel -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  (σ : FirstKindInvolution K D) {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
  (q : σ.QuadraticForms n)

/-- The exact isometry subgroup of tensor matrix units over a coefficient algebra. -/
abbrev tensorIsometryGroup (R : Type u) [CommRing R] [Algebra K R] :=
  IsometryCut.isometrySubgroup (τ := σ.matrix n) (M := σ.quadraticKernel n)
    IsometryCut.isStable_alternatingSubspace (Quotient.out q) R

/-- The norm on actual tensor isometry units. -/
def tensorIsometryNorm (R : Type u) [CommRing R] [Algebra K R] :
    σ.tensorIsometryGroup q R →* Rˣ :=
  (CentralSimple.reducedNormUnits K (Matrix n n D) R).comp
    (σ.tensorIsometryGroup q R).subtype

/-- The actual norm-one isometry subgroup in tensor coordinates. -/
abbrev tensorNormOneIsometryGroup (R : Type u) [CommRing R] [Algebra K R] :=
  (σ.tensorIsometryNorm q R).ker

/-- The affine coefficient points of the isometry group are its tensor isometry units. -/
def isometryAffinePointsEquiv (R : CommAlgCat.{u} (CommRingCat.of K)) :
    ((algSpec (CommRingCat.of K)).obj (op R) ⟶ (σ.isometryGroup q).X) ≃*
      σ.tensorIsometryGroup q R :=
  Corepresented.affinePointsEquiv _
    (Corepresented.cutCorepresentableBy
      (IsometryCut.isCutOutBy (τ := σ.matrix n) (M := σ.quadraticKernel n)
        IsometryCut.isStable_alternatingSubspace (Quotient.out q))) R

omit [Algebra.IsCentral K D] [Nonempty n] in
/-- This comparison has the prescribed actual ambient affine tensor unit. -/
theorem isometryAffinePointsEquiv_val (R : CommAlgCat.{u} (CommRingCat.of K))
    (x : (algSpec (CommRingCat.of K)).obj (op R) ⟶ (σ.isometryGroup q).X) :
    (σ.isometryAffinePointsEquiv q R x).val =
      FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D)) R
        (x ≫ (σ.isometryGroupι q).hom.hom) := by
  change _ = Corepresented.affinePointsEquiv _ (FiniteAlgebraUnits.corepresentableBy
    (Module.finBasis K (Matrix n n D))) R (x ≫ (Corepresented.cutHom _).hom.hom)
  rw [Corepresented.cutHom, Corepresented.groupSchemeMap_affinePoints]
  rfl

private def kernelCoordinateEquiv {M N M' N' : Type*}
    [Group M] [Group N] [Group M'] [Group N']
    (f : M →* N) (f' : M' →* N') (eM : M ≃* M') (eN : N ≃* N')
    (h : ∀ x, eN (f x) = f' (eM x)) : f.ker ≃* f'.ker where
  toFun x := ⟨eM x.val, by
    change f' (eM x.val) = 1
    rw [← h, x.property, _root_.map_one]⟩
  invFun x := ⟨eM.symm x.val, by
    apply eN.injective
    rw [h, eM.apply_symm_apply, x.property, _root_.map_one]⟩
  left_inv x := Subtype.ext (eM.symm_apply_apply x)
  right_inv x := Subtype.ext (eM.apply_symm_apply x)
  map_mul' x y := Subtype.ext (eM.map_mul x y)

/-- Affine points of the actual group-scheme kernel are exactly the tensor
isometry units whose canonical reduced norm is one. -/
def normOneIsometryAffinePointsEquiv (R : CommAlgCat.{u} (CommRingCat.of K)) :
    ((algSpec (CommRingCat.of K)).obj (op R) ⟶ (σ.normOneIsometryGroup q).X) ≃*
      σ.tensorNormOneIsometryGroup q R :=
  (kernelPointsEquiv (σ.isometryGroupι q ≫
      CentralSimpleUnits.reducedNormHom K (Matrix n n D))
    ((algSpec (CommRingCat.of K)).obj (op R))).trans
      (kernelCoordinateEquiv _ _ (σ.isometryAffinePointsEquiv q R)
        (Gm.affinePointsEquiv ((algSpec (CommRingCat.of K)).obj (op R)).hom) (fun x => by
          change Gm.affinePointsEquiv ((algSpec (CommRingCat.of K)).obj (op R)).hom
            (x ≫ (σ.isometryGroupι q ≫
              CentralSimpleUnits.reducedNormHom K (Matrix n n D)).hom.hom) = _
          rw [Grp.comp_hom_hom, ← Category.assoc,
            CentralSimpleUnits.reducedNormHom_affine_points,
            ← isometryAffinePointsEquiv_val]
          rfl))

/-- The affine norm-one comparison commutes with the actual ambient inclusion. -/
theorem normOneIsometryAffinePointsEquiv_val (R : CommAlgCat.{u} (CommRingCat.of K))
    (x : (algSpec (CommRingCat.of K)).obj (op R) ⟶ (σ.normOneIsometryGroup q).X) :
    (σ.normOneIsometryAffinePointsEquiv q R x).val.val =
      FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D)) R
        (x ≫ (σ.normOneIsometryAmbientι q).hom.hom) := by
  change (σ.isometryAffinePointsEquiv q R
    (x ≫ (σ.normOneIsometryGroupι q).hom.hom)).val = _
  rw [isometryAffinePointsEquiv_val, normOneIsometryAmbientι, Grp.comp_hom_hom,
    Category.assoc]

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
