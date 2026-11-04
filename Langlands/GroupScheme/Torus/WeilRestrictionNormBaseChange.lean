import Langlands.GroupScheme.Torus.WeilRestrictionNormOne
import Langlands.GroupScheme.Torus.WeilRestrictionBaseChange

/-! # Arbitrary base change of the finite-free norm and its norm-one kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilGm

section Algebraic

variable (A A' B R : Type u) [CommRing A] [CommRing A'] [CommRing B] [CommRing R]
  [Algebra A A'] [Algebra A B] [Algebra A' R] [Algebra A R] [IsScalarTower A A' R]

/-- The tensor determinant norm is unchanged by the canonical base-change equivalence. -/
theorem tensorNorm_baseChange (x : B ⊗[A] R) :
    Langlands.Algebra.tensorNorm A' (A' ⊗[A] B) R (baseChangeTensorEquiv A A' B R x) =
      Langlands.Algebra.tensorNorm A B R x := by
  change Algebra.norm R ((Algebra.TensorProduct.comm A' (A' ⊗[A] B) R)
    ((Algebra.TensorProduct.comm A' R (A' ⊗[A] B))
      ((Algebra.TensorProduct.cancelBaseChange A A' R R B).symm
        (Algebra.TensorProduct.comm A B R x)))) = _
  rw [← Algebra.TensorProduct.comm_symm A' R (A' ⊗[A] B), AlgEquiv.symm_apply_apply]
  exact Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.cancelBaseChange A A' R R B).symm
    (Algebra.TensorProduct.comm A B R x)

/-- The unit norm is unchanged by the canonical base-change equivalence. -/
theorem tensorNormUnits_baseChange (x : (B ⊗[A] R)ˣ) :
    Langlands.Algebra.tensorNormUnits A' (A' ⊗[A] B) R
        (Units.map (baseChangeTensorEquiv A A' B R).toMonoidHom x) =
      Langlands.Algebra.tensorNormUnits A B R x := by
  apply Units.ext
  exact tensorNorm_baseChange A A' B R x.val

/-- Tensor norm-one units are preserved by arbitrary base change. -/
def normOneTensorEquiv :
    (Langlands.Algebra.tensorNormUnits A B R).ker ≃*
      (Langlands.Algebra.tensorNormUnits A' (A' ⊗[A] B) R).ker where
  toFun x := ⟨Units.mapEquiv (baseChangeTensorEquiv A A' B R).toMulEquiv x.val, by
    change Langlands.Algebra.tensorNormUnits A' (A' ⊗[A] B) R (Units.map _ x.val) = 1
    exact (tensorNormUnits_baseChange A A' B R x.val).trans x.property⟩
  invFun y := ⟨(Units.mapEquiv (baseChangeTensorEquiv A A' B R).toMulEquiv).symm y.val, by
    change Langlands.Algebra.tensorNormUnits A B R
      ((Units.mapEquiv (baseChangeTensorEquiv A A' B R).toMulEquiv).symm y.val) = 1
    rw [← tensorNormUnits_baseChange A A' B R]
    change Langlands.Algebra.tensorNormUnits A' (A' ⊗[A] B) R
      ((Units.mapEquiv (baseChangeTensorEquiv A A' B R).toMulEquiv)
        ((Units.mapEquiv (baseChangeTensorEquiv A A' B R).toMulEquiv).symm y.val)) = 1
    rw [MulEquiv.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext
    ((Units.mapEquiv (baseChangeTensorEquiv A A' B R).toMulEquiv).symm_apply_apply x.val)
  right_inv y := Subtype.ext
    ((Units.mapEquiv (baseChangeTensorEquiv A A' B R).toMulEquiv).apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

@[simp] theorem normOneTensorEquiv_val
    (x : (Langlands.Algebra.tensorNormUnits A B R).ker) :
    (normOneTensorEquiv A A' B R x).val =
      Units.map (baseChangeTensorEquiv A A' B R).toMonoidHom x.val := rfl

end Algebraic

section Scheme

variable (A A' : CommRingCat.{u}) [Algebra A A'] (B : Type u) [CommRing B]
  [Algebra A B] [Module.Finite A B] [Module.Free A B]

/-- The actual finite-free norm commutes with arbitrary commutative-ring base change. -/
theorem norm_baseChange :
    (GroupScheme.baseChange (baseMap A A')).map (norm A B) ≫
        (Gm.baseChangeIso (baseMap A A')).hom =
      (algebraBaseChangeIso A A' B).hom ≫ norm A' (A' ⊗[A] B) := by
  apply hom_ext_points
  intro T x
  apply (Gm.pointsEquiv (Spec A') T).injective
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [Gm.pointsEquiv_baseChangeIso_hom, Gm.baseChangeUnitsEquiv_apply,
    GroupScheme.baseChangePointsEquiv_comp, norm_points, norm_points,
    algebraBaseChangeIso_hom_points]
  exact (tensorNormUnits_baseChange A A' B (restrictedSections A A' T) _).symm

/-- Norm-one points after base change, in the tensor norm-one model over the new base. -/
def baseNormOnePointsEquiv (T : Over (Spec A')) :
    (T ⟶ ((GroupScheme.baseChange (baseMap A A')).obj (normOne A B)).X) ≃*
      (Langlands.Algebra.tensorNormUnits A' (A' ⊗[A] B) ((algΓ A').obj T).unop).ker :=
  (GroupScheme.baseChangePointsEquiv (baseMap A A') (normOne A B) T).trans
    ((normOnePointsEquiv A B ((Over.map (baseMap A A')).obj T)).trans
      (normOneTensorEquiv A A' B (restrictedSections A A' T)))

/-- The new norm-one model is the base-changed Weil-unit model of the included point. -/
theorem baseNormOnePointsEquiv_val (T : Over (Spec A'))
    (x : T ⟶ ((GroupScheme.baseChange (baseMap A A')).obj (normOne A B)).X) :
    (baseNormOnePointsEquiv A A' B T x).val =
      basePointsEquiv A A' B T
        (x ≫ ((GroupScheme.baseChange (baseMap A A')).map (normOneι A B)).hom.hom) := by
  change Units.map (baseChangeTensorEquiv A A' B (restrictedSections A A' T)).toMonoidHom
    (normOnePointsEquiv A B ((Over.map (baseMap A A')).obj T)
      (GroupScheme.baseChangePointsEquiv (baseMap A A') (normOne A B) T x)).val = _
  rw [normOnePointsEquiv_val, basePointsEquiv_apply, GroupScheme.baseChangePointsEquiv_comp]

/-- The base-changed norm-one model is natural on all test schemes. -/
theorem baseNormOnePointsEquiv_naturality {T T' : Over (Spec A')} (a : T' ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange (baseMap A A')).obj (normOne A B)).X) :
    baseNormOnePointsEquiv A A' B T' (a ≫ x) =
      normOneUnitsRestrict A' (A' ⊗[A] B) a (baseNormOnePointsEquiv A A' B T x) := by
  apply Subtype.ext
  change (baseNormOnePointsEquiv A A' B T' (a ≫ x)).val =
    Units.map (Algebra.TensorProduct.lTensor (S := A' ⊗[A] B) (A' ⊗[A] B)
      ((algΓ A').map a).unop.hom).toMonoidHom (baseNormOnePointsEquiv A A' B T x).val
  rw [baseNormOnePointsEquiv_val, baseNormOnePointsEquiv_val, Category.assoc,
    basePointsEquiv_naturality]
  rfl

/-- The actual norm-one kernel commutes with arbitrary commutative-ring base change. -/
def normOneAlgebraBaseChangeIso :
    (GroupScheme.baseChange (baseMap A A')).obj (normOne A B) ≅
      normOne A' (A' ⊗[A] B) :=
  isoOfPointModels
    (fun T : Over (Spec A') =>
      (Langlands.Algebra.tensorNormUnits A' (A' ⊗[A] B) ((algΓ A').obj T).unop).ker)
    (fun a => normOneUnitsRestrict A' (A' ⊗[A] B) a)
    (baseNormOnePointsEquiv A A' B) (normOnePointsEquiv A' (A' ⊗[A] B))
    (fun a x => baseNormOnePointsEquiv_naturality A A' B a x)
    (fun a y => normOnePointsEquiv_naturality A' (A' ⊗[A] B) a y)

/-- On every test, the norm-one isomorphism is the canonical tensor equivalence
restricted to units of norm one. -/
theorem normOneAlgebraBaseChangeIso_hom_points (T : Over (Spec A'))
    (x : T ⟶ ((GroupScheme.baseChange (baseMap A A')).obj (normOne A B)).X) :
    normOnePointsEquiv A' (A' ⊗[A] B) T
        (x ≫ (normOneAlgebraBaseChangeIso A A' B).hom.hom.hom) =
      normOneTensorEquiv A A' B (restrictedSections A A' T)
        (normOnePointsEquiv A B ((Over.map (baseMap A A')).obj T)
          (GroupScheme.baseChangePointsEquiv (baseMap A A') (normOne A B) T x)) :=
  isoOfPointModels_hom
    (fun T : Over (Spec A') =>
      (Langlands.Algebra.tensorNormUnits A' (A' ⊗[A] B) ((algΓ A').obj T).unop).ker)
    (fun a => normOneUnitsRestrict A' (A' ⊗[A] B) a)
    (baseNormOnePointsEquiv A A' B) (normOnePointsEquiv A' (A' ⊗[A] B))
    (fun a x => baseNormOnePointsEquiv_naturality A A' B a x)
    (fun a y => normOnePointsEquiv_naturality A' (A' ⊗[A] B) a y) T x

/-- The norm-one base-change isomorphism respects the actual subgroup inclusion. -/
theorem normOneAlgebraBaseChangeIso_hom_ι :
    (normOneAlgebraBaseChangeIso A A' B).hom ≫ normOneι A' (A' ⊗[A] B) =
      (GroupScheme.baseChange (baseMap A A')).map (normOneι A B) ≫
        (algebraBaseChangeIso A A' B).hom := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv A' (A' ⊗[A] B) T).injective
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [← normOnePointsEquiv_val, normOneAlgebraBaseChangeIso_hom_points,
    normOneTensorEquiv_val, normOnePointsEquiv_val, algebraBaseChangeIso_hom_points,
    GroupScheme.baseChangePointsEquiv_comp]

end Scheme

section RingMap

variable {A A' : CommRingCat.{u}} (f : A ⟶ A') (B : Type u) [CommRing B]
  [Algebra A B] [Module.Finite A B] [Module.Free A B]

/-- The actual norm square along any ring map, using its induced algebra structure. -/
theorem norm_baseChange_specMap :
    letI := f.hom.toAlgebra
    (GroupScheme.baseChange (Spec.map f)).map (norm A B) ≫
        (Gm.baseChangeIso (Spec.map f)).hom =
      (baseChangeIso f B).hom ≫ norm A' (A' ⊗[A] B) := by
  let _ := f.hom.toAlgebra
  exact norm_baseChange A A' B

/-- Base change of the actual norm-one group scheme along an arbitrary ring map. -/
def normOneBaseChangeIso :
    letI := f.hom.toAlgebra
    (GroupScheme.baseChange (Spec.map f)).obj (normOne A B) ≅
      normOne A' (A' ⊗[A] B) :=
  letI := f.hom.toAlgebra
  normOneAlgebraBaseChangeIso A A' B

set_option maxRecDepth 4000 in
/-- The arbitrary-ring-map isomorphism is the canonical tensor equivalence on
all norm-one test points. -/
theorem normOneBaseChangeIso_hom_points (T : Over (Spec A'))
    (x : T ⟶ ((GroupScheme.baseChange (Spec.map f)).obj (normOne A B)).X) :
    letI := f.hom.toAlgebra
    normOnePointsEquiv A' (A' ⊗[A] B) T
        (x ≫ (normOneBaseChangeIso f B).hom.hom.hom) =
      normOneTensorEquiv A A' B (restrictedSections A A' T)
        (normOnePointsEquiv A B ((Over.map (Spec.map f)).obj T)
          (GroupScheme.baseChangePointsEquiv (Spec.map f) (normOne A B) T x)) := by
  let _ := f.hom.toAlgebra
  exact normOneAlgebraBaseChangeIso_hom_points A A' B T x

/-- The arbitrary-ring-map isomorphism respects the actual norm-one inclusion. -/
theorem normOneBaseChangeIso_hom_ι :
    letI := f.hom.toAlgebra
    (normOneBaseChangeIso f B).hom ≫ normOneι A' (A' ⊗[A] B) =
      (GroupScheme.baseChange (Spec.map f)).map (normOneι A B) ≫
        (baseChangeIso f B).hom := by
  let _ := f.hom.toAlgebra
  exact normOneAlgebraBaseChangeIso_hom_ι A A' B

end RingMap

end Langlands.GroupScheme.WeilGm
